package main

import (
	"bufio"
	"bytes"
	"context"
	"crypto/aes"
	"crypto/cipher"
	"crypto/md5"
	"embed"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"golang.org/x/image/font"
	"golang.org/x/image/font/opentype"
	"golang.org/x/image/font/sfnt"
	"golang.org/x/image/math/fixed"
	"golang.org/x/image/vector"
	"golang.org/x/sys/windows"
	"hash/fnv"
	"html"
	"image"
	"image/color"
	"image/draw"
	"image/jpeg"
	"image/png"
	"io"
	"math"
	"math/rand"
	"mime/multipart"
	"net"
	"net/http"
	"net/http/cookiejar"
	"net/textproto"
	"net/url"
	"os"
	"os/signal"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"
	"unicode"
	"unicode/utf8"
	"unsafe"
)

type accountRequestGate struct {
	mu    sync.Mutex
	until time.Time
}

var accountRequestGates sync.Map

func (s *Session) SetAccount(username string) {
	key := strings.ToLower(strings.TrimSpace(username))
	if key == "" {
		return
	}
	gate, _ := accountRequestGates.LoadOrStore(key, &accountRequestGate{})
	s.gate = gate.(*accountRequestGate)
}

func (g *accountRequestGate) pause() {
	g.mu.Lock()
	defer g.mu.Unlock()
	g.until = time.Now().Add(5 * time.Second)
}

func (g *accountRequestGate) wait(ctx context.Context) error {
	for {
		if err := ctx.Err(); err != nil {
			return err
		}
		g.mu.Lock()
		delay := time.Until(g.until)
		g.mu.Unlock()
		if delay <= 0 {
			return nil
		}
		timer := time.NewTimer(delay)
		select {
		case <-ctx.Done():
			timer.Stop()
			return ctx.Err()
		case <-timer.C:
		}
	}
}

func validateOptionalBusiness(response *Response, stage string) error {
	contentType := strings.ToLower(response.Header.Get("Content-Type"))
	body := strings.TrimLeft(response.Text(), " \t\r\n")
	if !strings.Contains(contentType, "json") && !strings.HasPrefix(body, "{") {
		return nil
	}
	object, ok := response.JSONObject()
	if !ok {
		return nil
	}
	success, hasSuccess := object["success"].(bool)
	code := stringValue(object["code"])
	failedCode := object["code"] != nil && code != "0" && code != "200"
	if (hasSuccess && !success) || failedCode {
		message := Excerpt(stringValue(object["message"]), 300)
		if message == "" {
			message = "服务器拒绝了认证请求"
		}
		return &Error{Kind: KindAuth, Message: stage + "失败：" + message, Code: code}
	}
	return nil
}

type Client struct {
	Session   *Session
	Endpoints Endpoints
}

func (c *Client) requestJSON(ctx context.Context, req Request, requireResult bool) (map[string]any, error) {
	return c.requestJSONWithResponse(ctx, req, requireResult, nil)
}

func (c *Client) requestJSONWithResponse(ctx context.Context, req Request, requireResult bool, onResponse func(*Response, error)) (map[string]any, error) {
	for attempt := 0; ; attempt++ {
		if err := ctx.Err(); err != nil {
			return nil, err
		}
		payload, response, err := c.requestJSONOnce(ctx, req, requireResult)
		if onResponse != nil {
			onResponse(response, err)
		}
		if err == nil || ctx.Err() != nil || !IsTransient(err) {
			return payload, err
		}
		delay := requestRetryDelay(attempt)
		if onResponse == nil {
			c.Session.reportBusinessRetry(req, err, delay)
		}
		timer := time.NewTimer(delay)
		select {
		case <-ctx.Done():
			timer.Stop()
			return nil, ctx.Err()
		case <-timer.C:
		}
	}
}

func (c *Client) requestJSONOnce(ctx context.Context, req Request, requireResult bool) (payload map[string]any, response *Response, requestErr error) {
	if strings.Contains(req.URL, "/jcedutec/courseSource/") {
		req = c.prepareCourseRequest(req)
	}
	response, err := c.Session.Do(ctx, req)
	if err != nil {
		return nil, response, err
	}
	if response.Status == 401 || response.Status == 403 {
		return nil, response, newError(KindAuthExpired, "登录状态已失效，需要重新登录")
	}
	if response.Status >= 400 {
		excerpt := ""
		if object, ok := response.JSONObject(); ok {
			excerpt = Excerpt(stringValue(object["message"]), 200)
		}
		if excerpt != "" {
			excerpt = "：" + excerpt
		}
		return nil, response, &Error{Kind: KindAPI, Message: fmt.Sprintf("%s失败（HTTP %d）%s", req.Stage, response.Status, excerpt), Code: strconv.Itoa(response.Status), HTTPStatus: response.Status}
	}
	object, ok := response.JSONObject()
	if !ok {
		return nil, response, newError(KindFormat, req.Stage+"返回的不是有效 JSON 对象")
	}
	success, hasSuccess := object["success"]
	if !hasSuccess {
		return nil, response, newError(KindFormat, req.Stage+"响应缺少 success 字段")
	}
	code := stringValue(object["code"])
	failedCode := object["code"] != nil && code != "0" && code != "200"
	if success != true || failedCode {
		message := Excerpt(stringValue(object["message"]), 300)
		if message == "" {
			message = "服务器返回业务错误"
		}
		if code == "401" || code == "403" {
			return nil, response, &Error{Kind: KindAuthExpired, Message: "登录状态已失效：" + message, Code: code}
		}
		return nil, response, &Error{Kind: KindAPI, Message: req.Stage + "失败：" + message, Code: code}
	}
	if requireResult {
		if _, ok := object["result"]; !ok {
			return nil, response, newError(KindFormat, req.Stage+"响应缺少 result 字段")
		}
	}
	return object, response, nil
}

func (c *Client) ListCourses(ctx context.Context) ([]Course, error) {
	payload, err := c.requestJSON(ctx, Request{Method: "GET", URL: c.Endpoints.Courses, Stage: "获取课程列表", Params: c.requestParams()}, true)
	if err != nil {
		return nil, err
	}
	raw := payload["result"]
	if raw == nil {
		return []Course{}, nil
	}
	list, ok := raw.([]any)
	if !ok {
		return nil, newError(KindFormat, "获取课程列表的 result 不是数组")
	}
	order := make([]string, 0, len(list))
	unique := map[string]Course{}
	for index, entry := range list {
		item, ok := entry.(map[string]any)
		if !ok {
			return nil, newError(KindFormat, "第 "+strconv.Itoa(index+1)+" 条课程数据不是对象")
		}
		id := strings.TrimSpace(stringValue(item["id"]))
		if id == "" {
			return nil, newError(KindFormat, "第 "+strconv.Itoa(index+1)+" 条课程数据缺少 id")
		}
		course := Course{
			ID:       id,
			TypeName: firstText(item, "type_dictText", "typeName"),
			Name:     firstText(item, "courseName", "name", "title", "type_dictText"),
			Finished: isCourseFinished(item),
		}
		if course.Name == "" {
			course.Name = "课程 " + id
		}
		if n, ok := integerValue(item["total"]); ok {
			course.Total = &n
		}
		if n, ok := integerValue(item["donum"]); ok {
			course.Done = &n
		}
		if n, ok := integerValue(item["unCorrectNum"]); ok {
			course.Wrong = &n
		}
		previous, seen := unique[id]
		if !seen {
			order = append(order, id)
			unique[id] = course
		} else if previous.Finished && !course.Finished {
			unique[id] = course
		}
	}
	courses := make([]Course, 0, len(order))
	for _, id := range order {
		courses = append(courses, unique[id])
	}
	return courses, nil
}

func (c *Client) ListQuestions(ctx context.Context, courseID string) ([]Question, error) {
	params := c.requestParams()
	params.Set("id", courseID)
	payload, err := c.requestJSON(ctx, Request{Method: "GET", URL: c.Endpoints.Questions, Stage: "获取课程题目", Params: params}, true)
	if err != nil {
		return nil, err
	}
	return parseQuestions(payload["result"], "获取课程题目")
}

func (c *Client) CourseDetail(ctx context.Context, courseID string) (CourseDetail, error) {
	params := c.requestParams()
	params.Set("id", courseID)
	payload, err := c.requestJSON(ctx, Request{Method: "GET", URL: c.Endpoints.CourseDetail, Stage: "获取课程详情", Params: params}, true)
	if err != nil {
		return CourseDetail{}, err
	}
	raw, ok := payload["result"].(map[string]any)
	if !ok {
		return CourseDetail{}, newError(KindFormat, "获取课程详情的 result 不是对象")
	}
	return parseCourseDetail(raw), nil
}

func (c *Client) UpdateVisits(ctx context.Context, courseID string) error {
	_, err := c.requestJSON(ctx, Request{Method: "POST", URL: c.Endpoints.VisitCourse, Stage: "记录课程访问", JSON: map[string]any{"id": courseID}}, false)
	return err
}

func (c *Client) ReportProgress(ctx context.Context, courseID string, seconds float64) error {
	return c.ReportProgressWithResponse(ctx, courseID, seconds, nil)
}

func (c *Client) ReportProgressWithResponse(ctx context.Context, courseID string, seconds float64, onResponse func(*Response, error)) error {
	_, err := c.requestJSONWithResponse(ctx, Request{Method: "POST", URL: c.Endpoints.ReportProgress, Stage: "上报观看进度", JSON: map[string]any{"id": courseID, "watchDuration": strconv.FormatFloat(seconds, 'f', -1, 64)}}, false, onResponse)
	return err
}

func (c *Client) SubmitAnswer(ctx context.Context, courseID string, question Question) error {
	return c.SubmitAnswerWithResponse(ctx, courseID, question, nil)
}

func (c *Client) SubmitAnswerWithResponse(ctx context.Context, courseID string, question Question, onResponse func(*Response, error)) error {
	_, err := c.requestJSONWithResponse(ctx, Request{Method: "POST", URL: c.Endpoints.SubmitAnswer, Stage: "提交题目答案", JSON: map[string]any{"questionId": question.ID, "id": courseID, "option": question.Option}}, false, onResponse)
	return err
}

func (c *Client) FinishCourse(ctx context.Context, courseID string) error {
	return c.FinishCourseWithResponse(ctx, courseID, nil)
}

func (c *Client) FinishCourseWithResponse(ctx context.Context, courseID string, onResponse func(*Response, error)) error {
	_, err := c.requestJSONWithResponse(ctx, Request{Method: "POST", URL: c.Endpoints.FinishCourse, Stage: "标记课程完成", JSON: map[string]any{"id": courseID}}, false, onResponse)
	return err
}

func (c *Client) ListExams(ctx context.Context) ([]ExamDefinition, error) {
	params := c.requestParams()

	params.Set("_t", strconv.FormatInt(time.Now().Unix(), 10))

	params.Set("pageNo", "1")
	params.Set("pageSize", "100")
	payload, err := c.requestJSON(ctx, Request{Method: "GET", URL: c.Endpoints.Exams, Stage: "获取考试列表", Params: params, Headers: map[string]string{"tenant-id": "0"}}, true)
	if err != nil {
		return nil, err
	}
	result, ok := payload["result"].(map[string]any)
	if !ok {
		return nil, newError(KindFormat, "获取考试列表的 result 不是对象")
	}
	records, ok := result["records"].([]any)
	if !ok {
		return nil, newError(KindFormat, "获取考试列表响应的 records 不是数组")
	}
	exams := make([]ExamDefinition, 0, len(records))
	for index, entry := range records {
		item, ok := entry.(map[string]any)
		if !ok {
			return nil, newError(KindFormat, "第 "+strconv.Itoa(index+1)+" 条考试数据不是对象")
		}
		id := strings.TrimSpace(stringValue(item["id"]))
		if id == "" {
			return nil, newError(KindFormat, "第 "+strconv.Itoa(index+1)+" 条考试数据缺少 id")
		}
		start, err := parseDateTime(item["startTime"], index+1)
		if err != nil {
			return nil, err
		}
		end, err := parseDateTime(item["endTime"], index+1)
		if err != nil {
			return nil, err
		}
		limit, err := requiredInteger(item["examNum"], "examNum", index+1)
		if err != nil {
			return nil, err
		}
		used, err := requiredInteger(item["useCount"], "useCount", index+1)
		if err != nil {
			return nil, err
		}
		qualified, err := optionalNumber(item["qualifiedScore"], "qualifiedScore", index+1)
		if err != nil {
			return nil, err
		}
		if qualified == nil {
			return nil, newError(KindFormat, "第 "+strconv.Itoa(index+1)+" 条考试数据缺少 qualifiedScore")
		}
		score, err := optionalNumber(item["score"], "score", index+1)
		if err != nil {
			return nil, err
		}
		name := firstText(item, "examName", "name")
		if name == "" {
			name = "考试 " + strconv.Itoa(index+1)
		}
		exams = append(exams, ExamDefinition{ID: id, Name: name, StartTime: start, EndTime: end, AttemptLimit: limit, UsedAttempts: used, QualifiedScore: *qualified, Score: score})
	}
	return exams, nil
}

func (c *Client) StartExam(ctx context.Context, definition ExamDefinition) (*Exam, error) {
	payload, err := c.requestJSON(ctx, Request{Method: "POST", URL: c.Endpoints.StartExam, Stage: "开始考试", Headers: map[string]string{"tenant-id": "0"}, JSON: map[string]any{"id": definition.ID, "type": ExamType}}, true)
	if err != nil {
		return nil, err
	}
	result, ok := payload["result"].(map[string]any)
	if !ok {
		return nil, newError(KindFormat, "开始考试的 result 不是对象")
	}
	recordID := strings.TrimSpace(stringValue(result["id"]))
	if recordID == "" {
		return nil, newError(KindFormat, "开始考试响应缺少考试记录 id")
	}
	if _, ok := result["records"].([]any); !ok {
		return nil, newError(KindFormat, "开始考试响应的 records 不是数组")
	}
	questions, err := parseQuestions(result["records"], "开始考试")
	if err != nil {
		return nil, err
	}
	return &Exam{ID: recordID, ExamID: definition.ID, Questions: questions}, nil
}

func (c *Client) SubmitExam(ctx context.Context, exam *Exam) (*ExamResult, error) {
	suffix := ""

	answers := make(map[string]any, len(exam.Questions))
	for _, question := range exam.Questions {
		answers[question.ID] = question.Option
	}
	target := c.Endpoints.SubmitExam + "/" + url.PathEscape(exam.ID) + suffix
	payload, err := c.requestJSON(ctx, Request{Method: "POST", URL: target, Stage: "提交考试", Headers: map[string]string{"tenant-id": "0"}, JSON: answers}, true)
	if err != nil {
		return nil, err
	}
	result, ok := payload["result"].(map[string]any)
	if !ok {
		return nil, newError(KindFormat, "提交考试的 result 不是对象")
	}
	resultID := strings.TrimSpace(stringValue(result["id"]))
	if resultID == "" {
		return nil, newError(KindFormat, "提交考试响应缺少考试记录 id")
	}
	if result["examId"] == nil || stringValue(result["examId"]) != exam.ExamID {
		return nil, newError(KindFormat, "提交考试返回的 examId 与当前考试不一致")
	}
	qualified := isFinished(result["isQualified"])
	if !qualified {
		detail := ""
		if score := optionalText(result["score"]); score != "" {
			detail = "，得分 " + score
		}
		return nil, &Error{Kind: KindAPI, Message: "考试未合格" + detail, Code: "not-qualified"}
	}
	certificatePath := optionalText(result["qualifiedCertificate"])
	if certificatePath == "" {
		return nil, newError(KindFormat, "提交考试响应缺少合格证书路径")
	}
	return &ExamResult{ID: resultID, Score: optionalText(result["score"]), Qualified: true, CertificatePath: certificatePath}, nil
}

func (c *Client) ConfirmExamPassed(ctx context.Context, definition ExamDefinition, attempts int) (*ExamDefinition, error) {
	if attempts < 1 {
		attempts = 1
	}
	for attempt := 1; attempt <= attempts; attempt++ {
		exams, err := c.ListExams(ctx)
		if err != nil {
			return nil, err
		}
		for _, exam := range exams {
			if exam.ID == definition.ID && exam.Passed() {
				confirmed := exam
				return &confirmed, nil
			}
		}
		if attempt < attempts {
			delay := time.Duration(attempt) * 800 * time.Millisecond
			if delay > 4*time.Second {
				delay = 4 * time.Second
			}
			select {
			case <-ctx.Done():
				return nil, newError(KindNetwork, "确认考试结果已取消")
			case <-time.After(delay):
			}
		}
	}
	return nil, &Error{Kind: KindAPI, Message: "提交接口已返回合格证书，但考试列表未确认合格；请到平台核对，不要重复提交", Code: "unconfirmed"}
}

type MyInfo struct {
	Name             string
	Code             string
	StudentLevel     string
	CollegeID        string
	Major            string
	CommitmentPath   string
	CommitmentStatus string
}

func (c *Client) signedGet(ctx context.Context, endpoint, stage string, params map[string]string) (map[string]any, error) {
	all := map[string]string{}
	for key, value := range params {
		all[key] = value
	}
	timestamp := strconv.FormatInt(time.Now().Unix(), 10)

	all["_t"] = timestamp
	query := url.Values{}
	for key, value := range all {
		query.Set(key, value)
	}
	target := endpoint + "?" + query.Encode()

	headers := map[string]string{
		"tenant-id":   "0",
		"X-Sign":      JeecgSign(all),
		"X-TIMESTAMP": strconv.FormatInt(time.Now().UnixMilli(), 10),
		"Referer":     c.Endpoints.Referer,
	}
	return c.requestJSON(ctx, Request{Method: "GET", URL: target, Stage: stage, Headers: headers}, true)
}

func (c *Client) QueryMyInfo(ctx context.Context) (*MyInfo, error) {
	payload, err := c.signedGet(ctx, c.Endpoints.MyInfo, "读取平台学生信息", nil)
	if err != nil {
		return nil, err
	}
	record, ok := payload["result"].(map[string]any)
	if !ok {
		return nil, newError(KindFormat, "平台学生信息格式异常")
	}
	return &MyInfo{
		Name:             optionalText(record["name"]),
		Code:             optionalText(record["code"]),
		StudentLevel:     optionalText(record["studentLevel"]),
		CollegeID:        optionalText(record["collegeId"]),
		Major:            optionalText(record["major"]),
		CommitmentPath:   optionalText(record["commitmentPath"]),
		CommitmentStatus: optionalText(record["commitmentStatus"]),
	}, nil
}

func (c *Client) UploadFile(ctx context.Context, fileName string, data []byte, contentType string) (string, error) {
	var body bytes.Buffer
	writer := multipart.NewWriter(&body)
	if err := writer.WriteField("biz", "temp"); err != nil {
		return "", err
	}
	header := textproto.MIMEHeader{}
	header.Set("Content-Disposition", fmt.Sprintf(`form-data; name="file"; filename="%s"`, escapeQuotes(fileName)))
	header.Set("Content-Type", contentType)
	part, err := writer.CreatePart(header)
	if err != nil {
		return "", err
	}
	if _, err := part.Write(data); err != nil {
		return "", err
	}
	if err := writer.Close(); err != nil {
		return "", err
	}
	payload, err := c.requestJSON(ctx, Request{
		Method:      "POST",
		URL:         c.Endpoints.Upload,
		Stage:       "上传承诺书",
		Headers:     map[string]string{"X-Requested-With": "XMLHttpRequest", "Accept": "*/*", "Referer": c.Endpoints.Referer, "Origin": c.Endpoints.Origin},
		Body:        body.Bytes(),
		ContentType: writer.FormDataContentType(),
	}, false)
	if err != nil {
		return "", err
	}

	path := strings.TrimSpace(optionalText(payload["message"]))
	if !looksLikeStoredPath(path) {
		switch value := payload["result"].(type) {
		case string:
			path = strings.TrimSpace(value)
		case map[string]any:
			path = firstText(value, "path", "url", "filePath")
		}
	}
	if !looksLikeStoredPath(path) {
		return "", newError(KindFormat, "上传承诺书后平台没有返回文件路径")
	}
	return path, nil
}

func (c *Client) BindCommitment(ctx context.Context, path string) error {
	_, err := c.signedGet(ctx, c.Endpoints.UpdateMyInfo, "绑定承诺书", map[string]string{"commitmentPath": path})
	return err
}

func looksLikeStoredPath(value string) bool {
	return value != "" && len(value) < 512 && strings.Contains(value, ".") && !strings.ContainsAny(value, " \n<>")
}

func escapeQuotes(s string) string {
	return strings.NewReplacer("\\", "\\\\", `"`, "\\\"").Replace(s)
}

func (c *Client) prepareCourseRequest(req Request) Request {
	params := map[string]any{}
	if parsed, err := url.Parse(req.URL); err == nil {
		for key, values := range parsed.Query() {
			if key != "_t" && len(values) > 0 {
				params[key] = values[len(values)-1]
			}
		}
	}
	for key, values := range req.Params {
		if key != "_t" && len(values) > 0 {
			params[key] = values[len(values)-1]
		}
	}
	if body, ok := req.JSON.(map[string]any); ok {
		normalized := make(map[string]any, len(body))
		for key, value := range body {
			switch value.(type) {
			case int, int64, float64, json.Number:
				value = stringValue(value)
			}
			normalized[key] = value
			params[key] = value
		}
		req.JSON = normalized
	}
	headers := make(map[string]string, len(req.Headers)+5)
	for key, value := range req.Headers {
		headers[key] = value
	}
	headers["tenant-id"] = "0"
	headers["X-Sign"] = courseSign(params)
	headers["X-TIMESTAMP"] = strconv.FormatInt(time.Now().UnixMilli(), 10)
	if c.Endpoints.Origin != "" {
		headers["Origin"] = c.Endpoints.Origin
	}

	headers["Referer"] = IntranetReferer

	req.Headers = headers
	if req.JSON != nil {
		req.ContentType = "application/json;charset=UTF-8"
	}
	if req.Method == http.MethodGet {
		query := url.Values{}
		for key, values := range req.Params {
			query[key] = append([]string(nil), values...)
		}
		if query.Get("_t") == "" {
			query.Set("_t", strconv.FormatInt(time.Now().Unix(), 10))
		}
		req.Params = query
	}
	return req
}

func courseSign(params map[string]any) string {
	var data bytes.Buffer
	encoder := json.NewEncoder(&data)
	encoder.SetEscapeHTML(false)
	_ = encoder.Encode(params)
	payload := strings.TrimSuffix(data.String(), "\n") + signatureSecret
	sum := md5.Sum([]byte(payload))
	return strings.ToUpper(hex.EncodeToString(sum[:]))
}

func EncryptCredential(text, checkKey string) (string, error) {
	key := []byte("iam" + checkKey)
	if len(key) != 16 && len(key) != 24 && len(key) != 32 {
		return "", newError(KindAuth, "统一认证加密参数长度无效")
	}
	block, err := aes.NewCipher(key)
	if err != nil {
		return "", fmt.Errorf("aes: %w", err)
	}
	plain := []byte(text)
	padding := aes.BlockSize - len(plain)%aes.BlockSize
	plain = append(plain, bytes.Repeat([]byte{byte(padding)}, padding)...)
	out := make([]byte, len(plain))
	cipher.NewCBCEncrypter(block, key).CryptBlocks(out, plain)
	return hex.EncodeToString(out), nil
}

type Kind int

const (
	KindNetwork Kind = iota

	KindAuth

	KindAuthExpired

	KindAPI

	KindFormat

	KindUncertain
)

type Error struct {
	Kind    Kind
	Message string
	Code    string

	HTTPStatus int
}

func (e *Error) Error() string { return e.Message }

func newError(kind Kind, message string) *Error { return &Error{Kind: kind, Message: message} }

func KindOf(err error) Kind {
	var pe *Error
	if errors.As(err, &pe) {
		return pe.Kind
	}
	return KindNetwork
}

func IsTransient(err error) bool {
	var pe *Error
	if !errors.As(err, &pe) {
		return true
	}
	switch pe.Kind {
	case KindNetwork, KindUncertain:
		return true
	case KindAPI:
		message := strings.ToLower(pe.Message)
		return pe.HTTPStatus == 429 || pe.HTTPStatus >= 500 || strings.Contains(message, "aquire lock fail") || strings.Contains(message, "acquire lock fail")
	default:
		return false
	}
}

type Course struct {
	ID       string `json:"id"`
	Name     string `json:"name"`
	TypeName string `json:"typeName,omitempty"`
	Finished bool   `json:"finished"`
	Total    *int   `json:"total,omitempty"`
	Done     *int   `json:"done,omitempty"`
	Wrong    *int   `json:"wrong,omitempty"`
}

type Question struct {
	ID        string `json:"id"`
	Kind      string `json:"kind"`
	EjectTime int    `json:"ejectTime,omitempty"`
	Option    any    `json:"option"`
}

type CourseDetail struct {
	ID       string
	Name     string
	Duration float64
}

var courseDurationKeys = []string{"duration", "watchDuration", "studyTime", "playTime", "videoDuration"}

func parseCourseDetail(raw map[string]any) CourseDetail {
	detail := CourseDetail{ID: strings.TrimSpace(stringValue(raw["id"])), Name: firstText(raw, "name", "courseName", "title")}
	for _, key := range courseDurationKeys {
		if seconds, ok := secondsValue(raw[key]); ok {
			detail.Duration = seconds
			break
		}
	}
	return detail
}

func CourseTargetSeconds(detail CourseDetail, questions []Question) float64 {
	if detail.Duration > 0 {
		return detail.Duration
	}
	last := 0
	for _, question := range questions {
		if question.EjectTime > last {
			last = question.EjectTime
		}
	}
	if last > 0 {
		return float64(last + 60)
	}
	return 60
}

type ExamDefinition struct {
	ID             string    `json:"id"`
	Name           string    `json:"name"`
	StartTime      time.Time `json:"startTime"`
	EndTime        time.Time `json:"endTime"`
	AttemptLimit   int       `json:"attemptLimit"`
	UsedAttempts   int       `json:"usedAttempts"`
	QualifiedScore float64   `json:"qualifiedScore"`
	Score          *float64  `json:"score,omitempty"`
}

func (e ExamDefinition) Available(now time.Time) bool {
	return e.UsedAttempts < e.AttemptLimit && !now.Before(e.StartTime) && !now.After(e.EndTime)
}

func (e ExamDefinition) Passed() bool {
	return e.Score != nil && *e.Score >= e.QualifiedScore
}

type Exam struct {
	ID        string
	ExamID    string
	Questions []Question
}

type ExamResult struct {
	ID              string
	Score           string
	Qualified       bool
	CertificatePath string
}

func stringValue(value any) string {
	switch v := value.(type) {
	case nil:
		return ""
	case string:
		return v
	case float64:
		if v == math.Trunc(v) && math.Abs(v) < 1e15 {
			return strconv.FormatInt(int64(v), 10)
		}
		return strconv.FormatFloat(v, 'f', -1, 64)
	case bool:
		if v {
			return "true"
		}
		return "false"
	case json.Number:
		return v.String()
	default:
		data, _ := json.Marshal(v)
		return string(data)
	}
}

func firstText(item map[string]any, keys ...string) string {
	for _, key := range keys {
		if text := strings.TrimSpace(stringValue(item[key])); text != "" {
			return text
		}
	}
	return ""
}

func optionalText(value any) string {
	return strings.TrimSpace(stringValue(value))
}

func integerValue(value any) (int, bool) {
	switch v := value.(type) {
	case bool:
		if v {
			return 1, true
		}
		return 0, true
	case float64:
		if v == math.Trunc(v) {
			return int(v), true
		}
		return 0, false
	case json.Number:
		if n, err := v.Int64(); err == nil {
			return int(n), true
		}
		if f, err := v.Float64(); err == nil && f == math.Trunc(f) {
			return int(f), true
		}
		return 0, false
	case string:
		n, err := strconv.Atoi(strings.TrimSpace(v))
		return n, err == nil
	default:
		return 0, false
	}
}

func secondsValue(value any) (float64, bool) {
	switch v := value.(type) {
	case float64:
		if v > 0 && !math.IsNaN(v) && !math.IsInf(v, 0) {
			return v, true
		}
	case json.Number:
		if f, err := v.Float64(); err == nil && f > 0 && !math.IsNaN(f) && !math.IsInf(f, 0) {
			return f, true
		}
	case string:
		if f, err := strconv.ParseFloat(strings.TrimSpace(v), 64); err == nil && f > 0 && !math.IsNaN(f) && !math.IsInf(f, 0) {
			return f, true
		}
	}
	return 0, false
}

func isFinished(value any) bool {
	switch v := value.(type) {
	case string:
		switch strings.ToLower(strings.TrimSpace(v)) {
		case "1", "true", "yes":
			return true
		}
		return false
	case bool:
		return v
	case float64:
		return v == 1
	default:
		return false
	}
}

func isCourseFinished(item map[string]any) bool {
	total, okTotal := integerValue(item["total"])
	done, okDone := integerValue(item["donum"])
	wrong, okWrong := integerValue(item["unCorrectNum"])
	return isFinished(item["isFinish"]) && okTotal && okDone && done == total && okWrong && wrong == 0
}

var letterPattern = regexp.MustCompile(`[A-D]`)

func answerChoices(answer any) map[string]bool {
	var values []any
	switch v := answer.(type) {
	case string:
		text := strings.TrimSpace(v)
		var decoded any
		if err := json.Unmarshal([]byte(text), &decoded); err == nil {
			if list, ok := decoded.([]any); ok {
				values = list
			}
		}
		if values == nil {
			for _, letter := range letterPattern.FindAllString(strings.ToUpper(text), -1) {
				values = append(values, letter)
			}
		}
	case []any:
		values = v
	default:
		values = []any{answer}
	}
	choices := map[string]bool{}
	for _, value := range values {
		choice := strings.ToUpper(strings.TrimSpace(stringValue(value)))
		if choice == "A" || choice == "B" || choice == "C" || choice == "D" {
			choices[choice] = true
		}
	}
	return choices
}

func answerOption(answer any, kind string, index int) (any, error) {
	choices := answerChoices(answer)
	if len(choices) == 0 {
		return nil, newError(KindFormat, "第 "+strconv.Itoa(index)+" 道题目的 correctAnswer 无效")
	}
	if kind == "1" || kind == "2" {
		if len(choices) != 1 {
			return nil, newError(KindFormat, "第 "+strconv.Itoa(index)+" 道单选/判断题的 correctAnswer 不是单个选项")
		}
		keys := make([]string, 0, 1)
		for key := range choices {
			keys = append(keys, key)
		}
		sort.Strings(keys)
		return keys[0], nil
	}

	ordered := make([]string, 0, len(choices))
	for _, letter := range []string{"A", "B", "C", "D"} {
		if choices[letter] {
			ordered = append(ordered, letter)
		}
	}
	return ordered, nil
}

func parseQuestions(raw any, label string) ([]Question, error) {
	if raw == nil {
		return []Question{}, nil
	}
	list, ok := raw.([]any)
	if !ok {
		return nil, newError(KindFormat, label+"的 result 不是数组")
	}
	questions := make([]Question, 0, len(list))
	for index, entry := range list {
		item, ok := entry.(map[string]any)
		if !ok {
			return nil, newError(KindFormat, "第 "+strconv.Itoa(index+1)+" 道题目数据不是对象")
		}

		id := strings.TrimSpace(stringValue(item["id"]))
		if id == "" {
			return nil, newError(KindFormat, "第 "+strconv.Itoa(index+1)+" 道题目缺少 id")
		}
		kind := strings.TrimSpace(stringValue(item["kind"]))
		if kind != "1" && kind != "2" && kind != "3" {
			if kind == "" {
				kind = "空"
			}
			return nil, newError(KindFormat, "第 "+strconv.Itoa(index+1)+" 道题目的 kind 不支持："+kind)
		}
		answer := item["correctAnswer"]
		if answer == nil || answer == "" {
			return nil, newError(KindFormat, "第 "+strconv.Itoa(index+1)+" 道题目缺少 correctAnswer")
		}
		if list, ok := answer.([]any); ok && len(list) == 0 {
			return nil, newError(KindFormat, "第 "+strconv.Itoa(index+1)+" 道题目缺少 correctAnswer")
		}
		option, err := answerOption(answer, kind, index+1)
		if err != nil {
			return nil, err
		}
		ejectTime := 0
		if seconds, ok := integerValue(item["ejectTime"]); ok && seconds > 0 {
			ejectTime = seconds
		}
		questions = append(questions, Question{ID: id, Kind: kind, EjectTime: ejectTime, Option: option})
	}
	return questions, nil
}

var timeLayouts = []string{"2006-01-02 15:04:05", "2006-01-02T15:04:05", "2006-01-02 15:04", "2006-01-02T15:04:05Z07:00", "2006-01-02"}

func parseDateTime(value any, index int) (time.Time, error) {
	text := strings.TrimSpace(stringValue(value))
	if text == "" {
		return time.Time{}, newError(KindFormat, "第 "+strconv.Itoa(index)+" 条考试数据缺少时间字段")
	}
	for _, layout := range timeLayouts {
		if parsed, err := time.ParseInLocation(layout, text, time.Local); err == nil {
			return parsed, nil
		}
	}
	return time.Time{}, newError(KindFormat, "第 "+strconv.Itoa(index)+" 条考试数据的时间格式无效")
}

func requiredInteger(value any, field string, index int) (int, error) {
	n, ok := integerValue(value)
	if !ok {
		return 0, newError(KindFormat, "第 "+strconv.Itoa(index)+" 条考试数据的 "+field+" 无效")
	}
	return n, nil
}

func optionalNumber(value any, field string, index int) (*float64, error) {
	switch v := value.(type) {
	case nil:
		return nil, nil
	case bool:
		return nil, newError(KindFormat, "第 "+strconv.Itoa(index)+" 条考试数据的 "+field+" 无效")
	case float64:
		if math.IsNaN(v) || math.IsInf(v, 0) {
			return nil, newError(KindFormat, "第 "+strconv.Itoa(index)+" 条考试数据的 "+field+" 无效")
		}
		return &v, nil
	case string:
		text := strings.TrimSpace(v)
		if text == "" {
			return nil, nil
		}
		f, err := strconv.ParseFloat(text, 64)
		if err != nil || math.IsNaN(f) || math.IsInf(f, 0) {
			return nil, newError(KindFormat, "第 "+strconv.Itoa(index)+" 条考试数据的 "+field+" 无效")
		}
		return &f, nil
	default:
		return nil, newError(KindFormat, "第 "+strconv.Itoa(index)+" 条考试数据的 "+field+" 无效")
	}
}

type Profile struct {
	Name        string
	College     string
	IDNumber    string
	StudentType string
	Source      string
}

const (
	SourceAcademic = "教务系统"
	SourceGraduate = "研究生系统"
)

func FetchProfile(ctx context.Context, session *Session, credentials Credentials, studentType string) (*Profile, error) {
	if studentType == "" {
		studentType = StudentTypeOf(credentials.Username)
	}
	if studentType == "undergraduate" {
		return fetchAcademicProfile(ctx, session, credentials)
	}
	return fetchGraduateProfile(ctx, session, credentials)
}

func fetchAcademicProfile(ctx context.Context, session *Session, credentials Credentials) (*Profile, error) {

	entry, err := openPage(ctx, session, credentials, AcademicSSOURL, "登录教务系统")
	if err != nil {
		return nil, err
	}
	if real, ok := campusRealURL(entry.FinalURL); !ok || !strings.EqualFold(real.Hostname(), "jwglxt.njupt.edu.cn") || strings.Contains(real.Path, "login_slogin") {
		return nil, newError(KindAuth, "教务系统没有接受当前登录（停在了 "+pageLabel(entry.FinalURL)+"）")
	}
	profile := &Profile{StudentType: "undergraduate", Source: SourceAcademic}

	homeURL := session.CampusURL(AcademicHomeInfoURL) + "?xt=jw&localeKey=zh_CN&_=" + strconv.FormatInt(time.Now().UnixMilli(), 10) + "&gnmkdm=index"

	if home, err := getHTML(ctx, session, homeURL, "读取教务系统首页", map[string]string{"X-Requested-With": "XMLHttpRequest", "Accept": "text/html, */*; q=0.01"}); err == nil {
		profile.Name, profile.College = ParseAcademicHome(home.Text())
	} else if IsTransient(err) {
		return nil, err
	}

	infoURL := session.CampusURL(AcademicProfileURL) + "?gnmkdm=N100801&layout=default"
	info, err := getHTML(ctx, session, infoURL, "读取教务系统个人信息", nil)
	if err != nil {
		return nil, err
	}
	fields := ParseAcademicProfile(info.Text())
	if fields["xm"] != "" {
		profile.Name = fields["xm"]
	}
	if profile.College == "" {
		profile.College = fields["jg_id"]
	}
	profile.IDNumber = strings.ToUpper(fields["zjhm"])
	if profile.IDNumber == "" {
		if strings.Contains(info.Text(), "login_slogin") || strings.Contains(info.FinalURL, "login_slogin") {
			return nil, newError(KindAuth, "教务系统会话无效，无法打开查询个人信息")
		}
		return nil, newError(KindFormat, "教务系统“查询个人信息”页面中没有找到证件号码")
	}
	return profile, nil
}

var (
	academicHeading = regexp.MustCompile(`(?s)<h4[^>]*class="media-heading"[^>]*>(.*?)</h4>`)
	academicLine    = regexp.MustCompile(`(?s)<div[^>]*class="media-body"[^>]*>.*?<p[^>]*>(.*?)</p>`)
	academicField   = regexp.MustCompile(`(?s)id="col_([A-Za-z0-9_]+)"[^>]*>\s*<p[^>]*class="form-control-static"[^>]*>(.*?)</p>`)
)

func ParseAcademicHome(page string) (name, college string) {
	if match := academicHeading.FindStringSubmatch(page); match != nil {
		name = strings.TrimSpace(strings.TrimSuffix(cleanText(match[1]), "学生"))
	}
	if match := academicLine.FindStringSubmatch(page); match != nil {
		if fields := strings.Fields(cleanText(match[1])); len(fields) > 0 {
			college = fields[0]
		}
	}
	return name, college
}

func ParseAcademicProfile(page string) map[string]string {
	fields := map[string]string{}
	for _, match := range academicField.FindAllStringSubmatch(page, -1) {
		if _, seen := fields[match[1]]; !seen {
			fields[match[1]] = cleanText(match[2])
		}
	}
	return fields
}

func fetchGraduateProfile(ctx context.Context, session *Session, credentials Credentials) (*Profile, error) {

	home, err := openPage(ctx, session, credentials, GraduateHomeURL, "登录研究生系统")
	if err != nil {
		return nil, err
	}
	if real, ok := campusRealURL(home.FinalURL); !ok || !strings.EqualFold(real.Hostname(), "yjs.njupt.edu.cn") {
		return nil, newError(KindAuth, "研究生系统没有接受当前登录（停在了 "+pageLabel(home.FinalURL)+"）")
	}
	page, err := openPage(ctx, session, credentials, GraduateProfileURL, "读取研究生系统学籍信息")
	if err != nil {
		return nil, err
	}
	profile := ParseGraduateProfile(page.Text())
	if profile.IDNumber == "" {
		return nil, newError(KindFormat, "研究生系统学籍信息页中没有找到证件号码")
	}
	return profile, nil
}

var (
	graduateCollege = regexp.MustCompile(`(?s)<span>\s*院系\s*</span>\s*<span[^>]*class="space"[^>]*>.*?</span>\s*<span[^>]*class="text"[^>]*>(.*?)</span>`)
	graduateInput   = regexp.MustCompile(`<input[^>]*\bname="(xm|zjhm)"[^>]*>`)
	inputValue      = regexp.MustCompile(`\bvalue="([^"]*)"`)
	graduateDetail  = regexp.MustCompile(`(?s)<label>\s*(姓\s*名|证件号码)：\s*</label>\s*<div[^>]*class="item-value detail"[^>]*>(.*?)</div>`)
	htmlTags        = regexp.MustCompile(`<[^>]*>`)
)

func ParseGraduateProfile(page string) *Profile {
	profile := &Profile{StudentType: "graduate", Source: SourceGraduate}
	if match := graduateCollege.FindStringSubmatch(page); match != nil {
		profile.College = cleanText(match[1])
	}
	for _, match := range graduateInput.FindAllStringSubmatch(page, -1) {
		value := inputValue.FindStringSubmatch(match[0])
		if value == nil {
			continue
		}
		switch match[1] {
		case "xm":
			if profile.Name == "" {
				profile.Name = cleanText(value[1])
			}
		case "zjhm":
			if profile.IDNumber == "" {
				profile.IDNumber = strings.ToUpper(cleanText(value[1]))
			}
		}
	}
	for _, match := range graduateDetail.FindAllStringSubmatch(page, -1) {
		label := strings.Join(strings.Fields(match[1]), "")
		value := cleanText(match[2])
		if label == "姓名" && profile.Name == "" {
			profile.Name = value
		}
		if label == "证件号码" && profile.IDNumber == "" {
			profile.IDNumber = strings.ToUpper(value)
		}
	}
	return profile
}

func cleanText(fragment string) string {
	return strings.Join(strings.Fields(html.UnescapeString(htmlTags.ReplaceAllString(fragment, " "))), " ")
}

var hasLetter = regexp.MustCompile(`[A-Za-z]`)

var fourteenDigits = regexp.MustCompile(`^\d{14}$`)

func StudentTypeOf(username string) string {
	username = strings.TrimSpace(username)
	if username == "" {
		return ""
	}
	if hasLetter.MatchString(username) || fourteenDigits.MatchString(username) {
		return "undergraduate"
	}
	return "graduate"
}

var idNumberPattern = regexp.MustCompile(`^\d{17}[\dXx]$|^\d{15}$`)

func ValidIDNumber(value string) bool {
	return idNumberPattern.MatchString(strings.TrimSpace(value))
}

func Excerpt(value string, limit int) string {
	text := strings.TrimSpace(strings.NewReplacer("\r", " ", "\n", " ").Replace(value))
	if limit > 0 && len([]rune(text)) > limit {
		return string([]rune(text)[:limit]) + "…"
	}
	return text
}

const htmlAccept = "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8"

var jwtPattern = regexp.MustCompile(`^eyJ[A-Za-z0-9_-]+\.[A-Za-z0-9_-]+\.[A-Za-z0-9_-]+$`)

func openPage(ctx context.Context, session *Session, credentials Credentials, pageURL, stage string) (*Response, error) {
	target := session.CampusURL(pageURL)
	response, err := getHTML(ctx, session, target, stage, nil)
	if err != nil {
		return nil, err
	}
	if base, serviceID, ok := casLoginPage(response.FinalURL); ok {
		serviceHost := ""
		if parsed, err := url.Parse(pageURL); err == nil {
			serviceHost = parsed.Hostname()
		}
		response, err = casSignIn(ctx, session, credentials, base, serviceID, serviceHost, stage)
		if err != nil {
			return nil, err
		}
		if _, _, still := casLoginPage(response.FinalURL); still {
			return nil, newError(KindAuth, stage+"：统一认证没有放行，可能需要验证码或账号无权访问该系统")
		}
	}
	return response, nil
}

func credentialPayload(credentials Credentials, appID string) (map[string]any, error) {
	username, err := EncryptCredential(credentials.Username, CheckKey)
	if err != nil {
		return nil, err
	}
	password, err := EncryptCredential(credentials.Password, CheckKey)
	if err != nil {
		return nil, err
	}
	return map[string]any{
		"checkKey":            CheckKey,
		"password":            password,
		"username":            username,
		"captchaVerification": nil,
		"appId":               appID,
		"mode":                "none",
	}, nil
}

func findString(value any, match func(key, value string) bool) string {
	var walk func(key string, node any) string
	walk = func(key string, node any) string {
		switch typed := node.(type) {
		case string:
			if match(key, typed) {
				return typed
			}
		case map[string]any:
			for childKey, child := range typed {
				if found := walk(childKey, child); found != "" {
					return found
				}
			}
		case []any:
			for _, child := range typed {
				if found := walk(key, child); found != "" {
					return found
				}
			}
		}
		return ""
	}
	return walk("", value)
}

type RequestEvent struct {
	Stage           string
	Method          string
	Status          int
	Elapsed         time.Duration
	Err             error
	Attempt         int
	Attempts        int
	CourseID        string
	RetryDelay      time.Duration
	RetryOnly       bool
	ProgressSeconds *float64
}

type Observer func(RequestEvent)

type Session struct {
	client   *http.Client
	jar      http.CookieJar
	headers  map[string]string
	observer Observer

	gate *accountRequestGate
	mu   sync.RWMutex
}

func (s *Session) SetHeader(name, value string) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.headers[name] = value
}

func (s *Session) Header(name string) string {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return s.headers[name]
}

func (s *Session) Cookie(rawURL, name string) string {
	u, err := url.Parse(rawURL)
	if err != nil {
		return ""
	}
	for _, cookie := range s.jar.Cookies(u) {
		if cookie.Name == name {
			return cookie.Value
		}
	}
	return ""
}

func (s *Session) SetCookie(rawURL, name, value string) {
	u, err := url.Parse(rawURL)
	if err != nil {
		return
	}
	s.jar.SetCookies(u, []*http.Cookie{{Name: name, Value: value, Path: "/"}})
}

type Request struct {
	Method  string
	URL     string
	Stage   string
	Params  url.Values
	Headers map[string]string
	JSON    any

	Body        []byte
	ContentType string

	NoRetry bool
}

type Response struct {
	Status   int
	Header   http.Header
	Body     []byte
	FinalURL string
	Elapsed  time.Duration
}

func (s *Session) Do(ctx context.Context, req Request) (*Response, error) {
	method := strings.ToUpper(req.Method)
	target := req.URL
	if len(req.Params) > 0 {
		separator := "?"
		if strings.Contains(target, "?") {
			separator = "&"
		}
		target += separator + req.Params.Encode()
	}
	var body []byte
	if req.JSON != nil {
		encoded, err := json.Marshal(req.JSON)
		if err != nil {
			return nil, newError(KindFormat, fmt.Sprintf("encode %s: %v", req.Stage, err))
		}
		body = encoded
	} else if req.Body != nil {
		body = req.Body
	}
	if _, err := http.NewRequestWithContext(ctx, method, target, nil); err != nil {
		return nil, newError(KindFormat, "请求格式无效："+err.Error())
	}
	retryAttempt := 0
	for attempt := 1; ; attempt++ {
		if err := s.gate.wait(ctx); err != nil {
			return nil, err
		}
		response, err := s.once(ctx, method, target, req, body)
		limited := response != nil && response.Status == http.StatusTooManyRequests
		if limited {
			s.gate.pause()
		}
		retry := err != nil || (response != nil && response.Status >= 500)
		delay := time.Duration(0)
		if limited {
			delay = 5 * time.Second
		} else if retry {
			delay = requestRetryDelay(retryAttempt)
			if response != nil {
				if after := parseRetryAfter(response.Header.Get("Retry-After")); after > delay {
					delay = after
				}
			}
		}
		if s.observer != nil {
			event := RequestEvent{Stage: req.Stage, Method: method, Attempt: attempt, Err: err, RetryDelay: delay, CourseID: requestCourseID(req), ProgressSeconds: requestProgressSeconds(req)}
			if response != nil {
				event.Status = response.Status
				event.Elapsed = response.Elapsed
			}
			s.observer(event)
		}

		if limited {
			continue
		}
		if !retry {
			return response, nil
		}
		if ctx.Err() != nil {
			return nil, ctx.Err()
		}
		retryAttempt++
		select {
		case <-ctx.Done():
			return nil, ctx.Err()
		case <-time.After(delay):
		}
	}
}

func requestRetryDelay(attempt int) time.Duration {
	delays := [...]time.Duration{time.Second, 2 * time.Second, 4 * time.Second, 8 * time.Second, 12 * time.Second}
	return delays[min(attempt, len(delays)-1)]
}

func requestCourseID(req Request) string {
	if !strings.Contains(req.URL, "/jcedutec/courseSource/") {
		return ""
	}
	if data, ok := req.JSON.(map[string]any); ok && data["id"] != nil {
		return stringValue(data["id"])
	}
	return req.Params.Get("id")
}

func requestProgressSeconds(req Request) *float64 {
	if data, ok := req.JSON.(map[string]any); ok && data["watchDuration"] != nil {
		if seconds, err := strconv.ParseFloat(stringValue(data["watchDuration"]), 64); err == nil {
			return &seconds
		}
	}
	return nil
}

func (s *Session) reportBusinessRetry(req Request, err error, delay time.Duration) {
	if s.observer != nil {
		s.observer(RequestEvent{Stage: req.Stage, Method: req.Method, Err: err, CourseID: requestCourseID(req), RetryDelay: delay, RetryOnly: true, ProgressSeconds: requestProgressSeconds(req)})
	}
}

func (s *Session) once(ctx context.Context, method, target string, req Request, body []byte) (*Response, error) {
	var reader io.Reader
	if body != nil {
		reader = bytes.NewReader(body)
	}
	httpReq, err := http.NewRequestWithContext(ctx, method, target, reader)
	if err != nil {
		return nil, err
	}
	s.mu.RLock()
	for name, value := range s.headers {
		httpReq.Header.Set(name, value)
	}
	s.mu.RUnlock()
	for name, value := range req.Headers {
		httpReq.Header.Set(name, value)
	}
	if httpReq.Header.Get("X-TIMESTAMP") != "" {
		httpReq.Header.Set("X-TIMESTAMP", strconv.FormatInt(time.Now().UnixMilli(), 10))
	}
	if body != nil {
		if req.JSON == nil && req.ContentType != "" {
			httpReq.Header.Set("Content-Type", req.ContentType)
		} else if req.JSON != nil && req.ContentType != "" {
			httpReq.Header.Set("Content-Type", req.ContentType)
		} else {
			httpReq.Header.Set("Content-Type", "application/json")
		}
	}
	started := time.Now()
	resp, err := s.client.Do(httpReq)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	data, err := io.ReadAll(io.LimitReader(resp.Body, 16<<20))
	if err != nil {
		return nil, err
	}
	final := target
	if resp.Request != nil && resp.Request.URL != nil {
		final = resp.Request.URL.String()
	}
	return &Response{Status: resp.StatusCode, Header: resp.Header, Body: data, FinalURL: final, Elapsed: time.Since(started)}, nil
}

func parseRetryAfter(value string) time.Duration {
	value = strings.TrimSpace(value)
	if value == "" {
		return 0
	}
	if seconds, err := strconv.Atoi(value); err == nil && seconds > 0 {
		return time.Duration(seconds) * time.Second
	}
	if at, err := http.ParseTime(value); err == nil {
		if d := time.Until(at); d > 0 {
			return d
		}
	}
	return 0
}

func (r *Response) JSONObject() (map[string]any, bool) {
	var payload any
	if err := json.Unmarshal(r.Body, &payload); err != nil {
		return nil, false
	}
	object, ok := payload.(map[string]any)
	return object, ok
}

func (r *Response) Text() string { return string(r.Body) }

func JeecgSign(params map[string]string) string {
	keys := make([]string, 0, len(params))
	for key := range params {
		if key != "_t" {
			keys = append(keys, key)
		}
	}
	sort.Strings(keys)
	var buffer bytes.Buffer
	buffer.WriteByte('{')
	for index, key := range keys {
		if index > 0 {
			buffer.WriteByte(',')
		}
		buffer.Write(jsonString(key))
		buffer.WriteByte(':')
		buffer.Write(jsonString(params[key]))
	}
	buffer.WriteByte('}')
	buffer.WriteString(signatureSecret)
	sum := md5.Sum(buffer.Bytes())
	return strings.ToUpper(hex.EncodeToString(sum[:]))
}

const signatureSecret = "dd05f1c54d63749eda95f9fa6d49v442a"

func jsonString(value string) []byte {
	var buffer bytes.Buffer
	encoder := json.NewEncoder(&buffer)
	encoder.SetEscapeHTML(false)
	_ = encoder.Encode(value)
	return bytes.TrimRight(buffer.Bytes(), "\n")
}

const (
	DPI        = 150
	PageWidth  = 1240
	PageHeight = 1754
	marginX    = 150
	marginTop  = 170
)

type Fields struct {
	College   string
	StudentID string
	IDNumber  string
	Name      string
}

type Template struct {
	Title      string
	Paragraphs []string
	Labels     []string
}

type Assets struct {
	Serif *sfnt.Font

	Handwriting []*Handwriting
	Template    Template

	Source string
}

type Handwriting struct {
	Key  string
	Name string
	Font *sfnt.Font
}

type Result struct {
	PNG           []byte
	JPEG          []byte
	MissingGlyphs []rune
	Font          *Handwriting
}

var bundledFontNames = map[string]string{
	"xingshu":  "瑞美加张清平硬笔行书",
	"chunfeng": "演示春风楷",
	"qiuhong":  "演示秋鸿楷",
}

func ParseTemplate(text string) Template {
	var template Template
	for _, raw := range strings.Split(strings.ReplaceAll(text, "\r", ""), "\n") {
		line := strings.TrimSpace(raw)
		if line == "" {
			continue
		}
		if strings.HasSuffix(line, "：") || strings.HasSuffix(line, ":") {
			template.Labels = append(template.Labels, line)
			continue
		}
		if template.Title == "" {
			template.Title = line
			continue
		}
		template.Paragraphs = append(template.Paragraphs, line)
	}
	return template
}

func Render(assets *Assets, fields Fields, fontKey string) (*Result, error) {
	hand := assets.Font(fontKey)
	if hand == nil {
		hand = assets.ChooseFont(fields, "", 0)
	}
	img := image.NewRGBA(image.Rect(0, 0, PageWidth, PageHeight))
	draw.Draw(img, img.Bounds(), image.White, image.Point{}, draw.Src)
	ink := color.RGBA{R: 26, G: 30, B: 38, A: 255}
	pen := color.RGBA{R: 20, G: 36, B: 104, A: 255}
	rule := color.RGBA{R: 70, G: 70, B: 70, A: 255}
	result := &Result{Font: hand}

	titleFace, err := newFace(assets.Serif, 26)
	if err != nil {
		return nil, err
	}
	bodyFace, err := newFace(assets.Serif, 14)
	if err != nil {
		return nil, err
	}
	labelFace := bodyFace

	y := marginTop + pt(26)
	titleWidth := advance(titleFace, assets.Template.Title)
	titleX := (PageWidth - titleWidth) / 2
	for dx := 0; dx <= 2; dx++ {
		for dy := 0; dy <= 1; dy++ {
			drawString(img, titleFace, ink, assets.Template.Title, titleX+dx, y+dy)
		}
	}

	y += pt(26) + pt(20)
	lineHeight := int(float64(pt(14)) * 1.75)
	contentWidth := PageWidth - 2*marginX
	for _, paragraph := range assets.Template.Paragraphs {
		indent := advance(bodyFace, "　　")
		lines := wrap(bodyFace, paragraph, contentWidth, indent)
		for index, line := range lines {
			x := marginX
			if index == 0 {
				x += indent
			}
			y += lineHeight
			drawString(img, bodyFace, ink, line, x, y)
		}
		y += lineHeight / 2
	}

	labels := assets.Template.Labels
	for len(labels) < 4 {
		labels = append(labels, []string{"所在学院：", "学　　号：", "身份证号：", "本人签字："}[len(labels)])
	}
	values := []string{fields.College, fields.StudentID, fields.IDNumber, fields.Name}
	blockTop := PageHeight - 720
	if y+80 > blockTop {
		blockTop = y + 80
	}

	x := PageWidth / 2
	labelWidth := 0
	for _, label := range labels {
		if w := advance(labelFace, label); w > labelWidth {
			labelWidth = w
		}
	}
	rowHeight := 92
	ruleWidth := PageWidth - marginX - (x + labelWidth + 12)
	for index, label := range labels {
		baseline := blockTop + index*rowHeight
		drawString(img, labelFace, ink, label, x, baseline)
		ruleX := x + labelWidth + 12

		for px := ruleX; px < ruleX+ruleWidth; px++ {
			img.Set(px, baseline+6, rule)
		}
		value := strings.TrimSpace(values[index])
		if value == "" {
			continue
		}
		size := 22.0
		if index == 3 {
			size = 34
		}
		size, err := fitSize(hand.Font, assets.Serif, bodyFace, size, value, ruleWidth-24)
		if err != nil {
			return nil, err
		}

		style := newPenStyle(fmt.Sprintf("%d|%s|%s|%s", index, value, fields.StudentID, hand.Key), index == 3)
		offset := []int{-6, -4, -5, -10}[index]
		missing := drawHandwritten(img, hand.Font, size, assets.Serif, bodyFace, pen, value, ruleX+14, baseline+offset, ruleWidth-24, style)
		result.MissingGlyphs = append(result.MissingGlyphs, missing...)
	}

	var pngBuffer, jpegBuffer bytes.Buffer
	if err := png.Encode(&pngBuffer, img); err != nil {
		return nil, err
	}
	if err := jpeg.Encode(&jpegBuffer, img, &jpeg.Options{Quality: 90}); err != nil {
		return nil, err
	}
	result.PNG = pngBuffer.Bytes()
	result.JPEG = jpegBuffer.Bytes()
	return result, nil
}

func pt(points float64) int { return int(points*DPI/72 + 0.5) }

func newFace(f *sfnt.Font, points float64) (font.Face, error) {
	return opentype.NewFace(f, &opentype.FaceOptions{Size: points, DPI: DPI, Hinting: font.HintingNone})
}

func advance(face font.Face, text string) int {
	return font.MeasureString(face, text).Ceil()
}

func drawString(img draw.Image, face font.Face, colour color.Color, text string, x, y int) {
	drawer := &font.Drawer{Dst: img, Src: image.NewUniform(colour), Face: face, Dot: fixed.P(x, y)}
	drawer.DrawString(text)
}

func fitSize(handwriting *sfnt.Font, fallbackFont *sfnt.Font, fallback font.Face, size float64, text string, maxWidth int) (float64, error) {
	var buffer sfnt.Buffer
	for scale := 1.0; scale >= 0.45; scale -= 0.05 {
		points := size * scale
		ppem := fixed.Int26_6(points * DPI / 72 * 64)
		width := 0.0
		for _, r := range text {
			if glyph, err := handwriting.GlyphIndex(&buffer, r); err == nil && glyph != 0 {
				adv, err := handwriting.GlyphAdvance(&buffer, glyph, ppem, font.HintingNone)
				if err != nil {
					return 0, err
				}
				width += float64(adv) / 64
			} else if hasGlyph(fallbackFont, &buffer, r) {
				width += float64(advance(fallback, string(r)))
			}
		}
		if width*1.04 <= float64(maxWidth) || scale-0.05 < 0.45 {
			return points, nil
		}
	}
	return size * 0.45, nil
}

type penStyle struct {
	rng        *rand.Rand
	slant      float64
	latinSlant float64
	rotation   float64
	wave       float64
	drift      float64
	signature  bool
}

func newPenStyle(seed string, signature bool) *penStyle {
	hash := fnv.New64a()
	hash.Write([]byte(seed))
	rng := rand.New(rand.NewSource(int64(hash.Sum64())))
	style := &penStyle{rng: rng, signature: signature}
	style.slant = 0.03 + rng.Float64()*0.07
	style.latinSlant = 0.05 + rng.Float64()*0.10
	style.rotation = (rng.Float64() - 0.5) * 1.6 * math.Pi / 180
	style.wave = 1 + rng.Float64()*1.5
	if signature {
		style.slant += 0.04
		style.wave += 1
	}
	return style
}

func (s *penStyle) nextBaseline(latin bool) float64 {
	step, noise, limit := s.wave*0.9, 1.6, s.wave*2.2
	if latin {
		step, noise, limit = s.wave*1.7, 3.0, s.wave*3.6
	}
	s.drift = s.drift*0.68 + (s.rng.Float64()-0.5)*2*step
	if s.drift > limit {
		s.drift = limit
	}
	if s.drift < -limit {
		s.drift = -limit
	}
	return s.drift + (s.rng.Float64()-0.5)*noise
}

func drawHandwritten(img *image.RGBA, handwriting *sfnt.Font, size float64, fallbackFont *sfnt.Font, fallback font.Face, pen color.RGBA, text string, x, y, maxWidth int, style *penStyle) []rune {
	var missing []rune
	var buffer sfnt.Buffer
	ppem := fixed.Int26_6(size * DPI / 72 * 64)
	runes := []rune(text)
	glyphs := make([]sfnt.GlyphIndex, len(runes))
	widths := make([]float64, len(runes))
	total := 0.0
	for index, r := range runes {
		if glyph, err := handwriting.GlyphIndex(&buffer, r); err == nil && glyph != 0 {
			glyphs[index] = glyph
			adv, err := handwriting.GlyphAdvance(&buffer, glyph, ppem, font.HintingNone)
			if err != nil {
				adv = ppem
			}

			spread := 0.12
			if isLatin(r) {
				spread = 0.34
			}
			widths[index] = float64(adv) / 64 * (1 - spread/2 + style.rng.Float64()*spread)
		} else if hasGlyph(fallbackFont, &buffer, r) {
			widths[index] = float64(advance(fallback, string(r)))
		} else {

			widths[index] = 0
			missing = append(missing, r)
		}
		total += widths[index]
	}
	squeeze := 1.0
	if total > float64(maxWidth) && total > 0 {
		squeeze = float64(maxWidth) / total
	}
	cursor := float64(x)
	for index, r := range runes {
		if widths[index] == 0 {
			continue
		}
		baseline := float64(y) + style.nextBaseline(isLatin(r))
		if glyphs[index] == 0 {
			drawString(img, fallback, pen, string(r), int(cursor), y)
		} else if err := drawPenGlyph(img, handwriting, &buffer, glyphs[index], ppem, cursor, baseline, style, pen, isLatin(r)); err != nil {

			_ = err
		}
		cursor += widths[index] * squeeze
	}
	return missing
}

func drawPenGlyph(img *image.RGBA, f *sfnt.Font, buffer *sfnt.Buffer, glyph sfnt.GlyphIndex, ppem fixed.Int26_6, ox, oy float64, style *penStyle, pen color.RGBA, latin bool) error {
	segments, err := f.LoadGlyph(buffer, glyph, ppem, nil)
	if err != nil {
		return err
	}
	if len(segments) == 0 {
		return nil
	}
	rng := style.rng
	jitter := 1.0
	if style.signature {
		jitter = 1.8
	}
	extraSlant := 0.0
	if latin {

		jitter = 2.9
		extraSlant = style.latinSlant
	}
	scale := 1 + (rng.Float64()-0.5)*0.10*jitter
	angle := style.rotation + (rng.Float64()-0.5)*2.4*jitter*math.Pi/180
	shear := style.slant + extraSlant + (rng.Float64()-0.5)*0.05*jitter
	sin, cos := math.Sin(angle), math.Cos(angle)
	transform := func(p fixed.Point26_6) [2]float64 {
		px := float64(p.X) / 64
		py := float64(p.Y) / 64
		px -= shear * py
		return [2]float64{(cos*px - sin*py) * scale, (sin*px + cos*py) * scale}
	}
	points := make([][2]float64, 0, len(segments)*3)
	minX, minY := math.Inf(1), math.Inf(1)
	maxX, maxY := math.Inf(-1), math.Inf(-1)
	for _, segment := range segments {
		for i := 0; i < segmentPoints(segment.Op); i++ {
			p := transform(segment.Args[i])
			points = append(points, p)
			minX, maxX = math.Min(minX, p[0]), math.Max(maxX, p[0])
			minY, maxY = math.Min(minY, p[1]), math.Max(maxY, p[1])
		}
	}
	x0 := int(math.Floor(ox+minX)) - 2
	y0 := int(math.Floor(oy+minY)) - 2
	width := int(math.Ceil(ox+maxX)) + 2 - x0
	height := int(math.Ceil(oy+maxY)) + 2 - y0
	if width <= 0 || height <= 0 {
		return nil
	}
	rect := image.Rect(x0, y0, x0+width, y0+height)
	if !rect.In(img.Bounds()) {
		return nil
	}

	pressure := rng.Float64()
	lift := uint8((1 - pressure) * 28)
	ink := color.NRGBA{R: pen.R + lift, G: pen.G + lift, B: pen.B + lift/2, A: uint8(200 + pressure*55)}
	raster := vector.NewRasterizer(width, height)
	raster.DrawOp = draw.Over
	stroke := func(dx, dy float64, colour color.NRGBA) {
		raster.Reset(width, height)
		i := 0
		at := func(k int) (float32, float32) {
			return float32(points[k][0] + ox - float64(x0) + dx), float32(points[k][1] + oy - float64(y0) + dy)
		}
		for _, segment := range segments {
			switch segment.Op {
			case sfnt.SegmentOpMoveTo:
				raster.MoveTo(at(i))
			case sfnt.SegmentOpLineTo:
				raster.LineTo(at(i))
			case sfnt.SegmentOpQuadTo:
				ax, ay := at(i)
				bx, by := at(i + 1)
				raster.QuadTo(ax, ay, bx, by)
			case sfnt.SegmentOpCubeTo:
				ax, ay := at(i)
				bx, by := at(i + 1)
				cx, cy := at(i + 2)
				raster.CubeTo(ax, ay, bx, by, cx, cy)
			}
			i += segmentPoints(segment.Op)
		}
		raster.ClosePath()
		raster.Draw(img, rect, image.NewUniform(colour), image.Point{})
	}
	stroke(0, 0, ink)
	if pressure > 0.5 {

		thick := ink
		thick.A = uint8(float64(ink.A) * 0.4)
		stroke(0.22, 0.18, thick)
	}
	return nil
}

func isLatin(r rune) bool {
	return r < 0x2E80 && !unicode.IsSpace(r)
}

func segmentPoints(op sfnt.SegmentOp) int {
	switch op {
	case sfnt.SegmentOpQuadTo:
		return 2
	case sfnt.SegmentOpCubeTo:
		return 3
	default:
		return 1
	}
}

func hasGlyph(f *sfnt.Font, buffer *sfnt.Buffer, r rune) bool {
	if f == nil {
		return false
	}
	glyph, err := f.GlyphIndex(buffer, r)
	return err == nil && glyph != 0
}

func wrap(face font.Face, text string, width, firstIndent int) []string {
	var lines []string
	var current strings.Builder
	currentWidth := firstIndent
	runes := []rune(text)
	for index := 0; index < len(runes); index++ {
		r := runes[index]
		w := advance(face, string(r))
		if currentWidth+w > width && current.Len() > 0 {

			if isNoStart(r) {
				current.WriteRune(r)
				lines = append(lines, current.String())
				current.Reset()
				currentWidth = 0
				continue
			}
			lines = append(lines, current.String())
			current.Reset()
			currentWidth = 0
		}
		current.WriteRune(r)
		currentWidth += w
	}
	if current.Len() > 0 {
		lines = append(lines, current.String())
	}
	return lines
}

func isNoStart(r rune) bool {
	return strings.ContainsRune("，。、；：？！）》」』”’…", r) || (unicode.IsPunct(r) && r < 0x3000)
}

func fontKey(name string) string {
	name = strings.TrimSuffix(name, ".gz")
	return strings.TrimSuffix(name, filepath.Ext(name))
}

func (a *Assets) Font(key string) *Handwriting {
	for _, hand := range a.Handwriting {
		if hand.Key == key {
			return hand
		}
	}
	return nil
}

func (a *Assets) ChooseFont(fields Fields, exclude string, roll uint64) *Handwriting {
	text := fields.College + fields.StudentID + fields.IDNumber + fields.Name
	var covering []*Handwriting
	var best *Handwriting
	bestMissing := -1
	var buffer sfnt.Buffer
	for _, hand := range a.Handwriting {
		missing := 0
		for _, r := range text {
			if unicode.IsSpace(r) {
				continue
			}
			if glyph, err := hand.Font.GlyphIndex(&buffer, r); err != nil || glyph == 0 {
				missing++
			}
		}
		if missing == 0 {
			covering = append(covering, hand)
		}
		if bestMissing < 0 || missing < bestMissing {
			best, bestMissing = hand, missing
		}
	}
	if len(covering) == 0 {
		return best
	}
	if len(covering) > 1 && exclude != "" {
		filtered := covering[:0:0]
		for _, hand := range covering {
			if hand.Key != exclude {
				filtered = append(filtered, hand)
			}
		}
		covering = filtered
	}
	return covering[roll%uint64(len(covering))]
}

func courseNameLess(a, b string) bool {
	a, b = strings.TrimSpace(a), strings.TrimSpace(b)
	for len(a) > 0 && len(b) > 0 {
		if a[0] >= '0' && a[0] <= '9' && b[0] >= '0' && b[0] <= '9' {
			i, j := 0, 0
			for i < len(a) && a[i] >= '0' && a[i] <= '9' {
				i++
			}
			for j < len(b) && b[j] >= '0' && b[j] <= '9' {
				j++
			}
			x, y := strings.TrimLeft(a[:i], "0"), strings.TrimLeft(b[:j], "0")
			if len(x) != len(y) {
				return len(x) < len(y)
			}
			if x != y {
				return x < y
			}
			a, b = a[i:], b[j:]
			continue
		}
		x, i := utf8.DecodeRuneInString(a)
		y, j := utf8.DecodeRuneInString(b)
		if unicode.ToLower(x) != unicode.ToLower(y) {
			return unicode.ToLower(x) < unicode.ToLower(y)
		}
		a, b = a[i:], b[j:]
	}
	return len(a) < len(b)
}

const (
	RequestTimeout      = 45 * time.Second
	ExamType            = "1"
	CheckKey            = "1629428467008"
	AppID               = "1816748629659033602"
	ServiceURL          = "http://10.22.192.38:9092/"
	IntranetOrigin      = "http://10.22.192.38:9092"
	IntranetReferer     = ServiceURL
	IntranetAPIBase     = "http://10.22.192.38:9090/jeecg-boot"
	AcademicSSOURL      = "http://jwglxt.njupt.edu.cn/sso/ddlogin"
	AcademicHomeInfoURL = "http://jwglxt.njupt.edu.cn/xtgl/index_cxYhxxIndex.html"
	AcademicProfileURL  = "http://jwglxt.njupt.edu.cn/xsxxxggl/xsgrxxwh_cxXsgrxx.html"
	GraduateHomeURL     = "https://yjs.njupt.edu.cn/allogene/page/home.htm"
	GraduateProfileURL  = "https://yjs.njupt.edu.cn/gl/page/student/studentBaseOne.htm"
	UserAgent           = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/151.0.0.0 Safari/537.36"
)

var version = "1.0.0"

var printMu sync.Mutex

var casAppIDs = map[string]string{"yjs.njupt.edu.cn": "1410894566680182785", "10.22.192.38": AppID}

type Credentials struct{ Username, Password string }

type Endpoints struct {
	Courses, CourseDetail, VisitCourse, ReportProgress, Questions, SubmitAnswer, FinishCourse string
	Exams, StartExam, SubmitExam, MyInfo, Upload, UpdateMyInfo, Referer, Origin               string
}

func IntranetEndpoints() Endpoints {
	base := IntranetAPIBase + "/jcedutec/"
	return Endpoints{
		Courses: base + "courseSource/myCourseList", CourseDetail: base + "courseSource/queryById",
		VisitCourse: base + "courseSource/updateVisits", ReportProgress: base + "courseSource/finishRate",
		Questions: base + "courseSource/queryCourseQuestionRelaByMainId", SubmitAnswer: base + "courseSource/submitAnswer", FinishCourse: base + "courseSource/finish",
		Exams: base + "exam/myExamList", StartExam: base + "exam/startExam", SubmitExam: base + "exam/submitExam",
		MyInfo: IntranetAPIBase + "/students/queryMyInfo", Upload: IntranetAPIBase + "/sys/common/upload", UpdateMyInfo: IntranetAPIBase + "/students/updateMyInfo",
		Referer: IntranetReferer + "students/questionList", Origin: IntranetOrigin,
	}
}

func NewSession(observer Observer) *Session {
	jar, _ := cookiejar.New(nil)
	dialer := &net.Dialer{Timeout: 10 * time.Second, KeepAlive: 30 * time.Second}
	transport := &http.Transport{DialContext: dialer.DialContext, MaxIdleConns: 8, MaxIdleConnsPerHost: 4, IdleConnTimeout: 60 * time.Second, TLSHandshakeTimeout: 15 * time.Second, ResponseHeaderTimeout: RequestTimeout, ForceAttemptHTTP2: true}
	client := &http.Client{Jar: jar, Transport: transport, Timeout: RequestTimeout}
	client.CheckRedirect = func(req *http.Request, via []*http.Request) error {
		if len(via) >= 20 {
			return errors.New("重定向次数过多")
		}
		if strings.EqualFold(req.URL.Hostname(), "i.njupt.edu.cn") && req.URL.Scheme == "http" {
			req.URL.Scheme = "https"
		}
		if req.URL.Host == "10.22.192.38:9092" && req.URL.Query().Get("ticket") != "" {
			return http.ErrUseLastResponse
		}
		return nil
	}
	return &Session{client: client, jar: jar, headers: map[string]string{"Accept": "application/json, text/plain, */*", "User-Agent": UserAgent}, observer: observer, gate: &accountRequestGate{}}
}

func (s *Session) CampusURL(raw string) string { return raw }

func campusRealURL(raw string) (*url.URL, bool) {
	u, err := url.Parse(raw)
	return u, err == nil && u.Host != ""
}

func pageLabel(raw string) string {
	u, ok := campusRealURL(raw)
	if ok {
		return u.Host + u.Path
	}
	return raw
}

func (c *Client) requestParams() url.Values { return url.Values{} }

func casLoginPage(final string) (string, string, bool) {
	u, ok := campusRealURL(final)
	if !ok || !strings.EqualFold(u.Hostname(), "i.njupt.edu.cn") {
		return "", "", false
	}
	id := u.Query().Get("service")
	if id == "" || strings.HasPrefix(strings.ToLower(id), "http") {
		return "", "", false
	}
	return u.Scheme + "://" + u.Host, id, true
}

func authRequest(ctx context.Context, session *Session, req Request) (*Response, error) {
	r, err := session.Do(ctx, req)
	if err != nil {
		return nil, err
	}
	if err := validateOptionalBusiness(r, req.Stage); err != nil {
		return nil, newError(KindAuth, r.Text())
	}
	if r.Status >= 400 {
		return nil, newError(KindAuth, r.Text())
	}
	return r, nil
}

func getHTML(ctx context.Context, session *Session, target, stage string, headers map[string]string) (*Response, error) {
	all := map[string]string{"Accept": htmlAccept, "Upgrade-Insecure-Requests": "1"}
	for key, value := range headers {
		all[key] = value
	}
	return authRequest(ctx, session, Request{Method: "GET", URL: target, Stage: stage, Headers: all})
}

func casSignIn(ctx context.Context, session *Session, credentials Credentials, base, serviceID, serviceHost, stage string) (*Response, error) {
	referer := base + "/user-login/user/login?service=" + url.QueryEscape(serviceID)
	headers := map[string]string{"tenant-id": "0", "Referer": referer, "Accept": "application/json, text/plain, */*", "Origin": base}
	appID := casAppIDs[strings.ToLower(serviceHost)]
	allocation := base + "/AppLoginAllocation/queryLoginAllocationByService?service=" + url.QueryEscape(serviceID) + "&_t=" + strconv.FormatInt(time.Now().Unix(), 10)
	if r, err := session.Do(ctx, Request{Method: "GET", URL: allocation, Stage: stage, Headers: headers}); err == nil {
		if object, ok := r.JSONObject(); ok {
			if found := findString(object, func(k, v string) bool { return strings.EqualFold(k, "appId") && v != "" }); found != "" {
				appID = found
			}
		}
	} else if ctx.Err() != nil {
		return nil, err
	}
	if appID == "" {
		appID = AppID
	}
	payload, err := credentialPayload(credentials, appID)
	if err != nil {
		return nil, err
	}
	r, err := authRequest(ctx, session, Request{Method: "POST", URL: base + "/ssoLogin/login", Stage: stage, JSON: payload, Headers: headers})
	if err != nil {
		return nil, err
	}
	if object, ok := r.JSONObject(); ok {
		tgc := findString(object, func(k, v string) bool { return strings.EqualFold(k, "tgc") && jwtPattern.MatchString(v) })
		if tgc == "" {
			tgc = findString(object, func(_ string, v string) bool { return jwtPattern.MatchString(v) })
		}
		if tgc != "" {
			session.SetCookie(base+"/", "tgc", tgc)
		}
	}
	return getHTML(ctx, session, base+"/ssoLogin/index?sessionId="+url.QueryEscape(serviceID), stage, map[string]string{"Referer": referer})
}

func serviceTicket(ctx context.Context, session *Session, credentials Credentials) (string, error) {
	r, err := authRequest(ctx, session, Request{Method: "GET", URL: "https://i.njupt.edu.cn/cas/login?service=" + url.QueryEscape(ServiceURL), Stage: "统一认证"})
	if err != nil {
		return "", err
	}
	if ticket, err := responseTicket(r); err == nil {
		return ticket, nil
	}
	base, serviceID, ok := casLoginPage(r.FinalURL)
	if !ok {
		return "", newError(KindAuth, "统一认证响应缺少 service："+r.Text())
	}
	r, err = casSignIn(ctx, session, credentials, base, serviceID, "10.22.192.38", "统一认证")
	if err != nil {
		return "", err
	}
	return responseTicket(r)
}

func responseTicket(r *Response) (string, error) {
	if location := r.Header.Get("Location"); location != "" {
		if u, err := url.Parse(location); err == nil && u.Host == "10.22.192.38:9092" {
			if ticket := u.Query().Get("ticket"); ticket != "" {
				return ticket, nil
			}
		}
	}
	u, err := url.Parse(r.FinalURL)
	if err == nil && u.Host == "10.22.192.38:9092" {
		if ticket := u.Query().Get("ticket"); ticket != "" {
			return ticket, nil
		}
	}
	return "", newError(KindAuth, "统一认证响应缺少 ticket："+r.Text())
}

func loginPlatform(ctx context.Context, credentials Credentials) (*Client, bool, error) {
	s := NewSession(nil)
	s.SetAccount(credentials.Username)
	ticket, err := serviceTicket(ctx, s, credentials)
	if err != nil {
		return nil, false, err
	}
	fmt.Println("登录SSO成功")
	params := map[string]string{"ticket": ticket, "service": ServiceURL}
	r, err := authRequest(ctx, s, Request{Method: "GET", URL: IntranetAPIBase + "/sys/cas/client/validateLogin", Stage: "登录实验室系统", Params: url.Values{"ticket": {ticket}, "service": {ServiceURL}, "_t": {strconv.FormatInt(time.Now().Unix(), 10)}}, Headers: map[string]string{"tenant-id": "0", "X-Sign": JeecgSign(params), "X-TIMESTAMP": strconv.FormatInt(time.Now().UnixMilli(), 10), "Origin": IntranetOrigin, "Referer": IntranetReferer}})
	if err != nil {
		return nil, true, err
	}
	object, ok := r.JSONObject()
	if !ok {
		return nil, true, newError(KindAuth, r.Text())
	}
	result, _ := object["result"].(map[string]any)
	token, _ := result["token"].(string)
	if strings.TrimSpace(token) == "" {
		return nil, true, newError(KindAuth, r.Text())
	}
	s.SetHeader("x-access-token", token)
	s.SetHeader("Origin", IntranetOrigin)
	s.SetHeader("Referer", IntranetReferer)
	s.observer = func(event RequestEvent) {
		if event.RetryDelay > 0 {
			logLine("warn", "%s：%s，%s 后继续重试", event.Stage, eventError(event), event.RetryDelay)
		}
	}
	fmt.Println("登录实验室系统成功")
	return &Client{Session: s, Endpoints: IntranetEndpoints()}, true, nil
}

func eventError(event RequestEvent) string {
	if event.Err != nil {
		return event.Err.Error()
	}
	return fmt.Sprintf("HTTP %d", event.Status)
}

func logLine(level, format string, args ...any) {
	printMu.Lock()
	defer printMu.Unlock()
	fmt.Printf("[%s] [%s] %s\n", time.Now().Format("15:04:05"), strings.ToUpper(level), fmt.Sprintf(format, args...))
}

func sleepContext(ctx context.Context, d time.Duration) error {
	timer := time.NewTimer(d)
	defer timer.Stop()
	select {
	case <-ctx.Done():
		return ctx.Err()
	case <-timer.C:
		return nil
	}
}

func courseRequestLogger(course Course, action string, seconds ...float64) func(*Response, error) {
	return func(_ *Response, err error) {
		if errors.Is(err, context.Canceled) {
			return
		}
		outcome, level, detail := "成功", "info", ""
		if len(seconds) > 0 {
			detail = fmt.Sprintf("，上报至 %s 秒", formatVideoSeconds(seconds[0]))
		}
		if err != nil {
			outcome, level = "失败", "warn"
			detail += "，原因：" + err.Error()
			if IsTransient(err) {
				detail += "，将继续重试"
			}
		}
		logLine(level, "课程「%s」%s请求%s%s", course.Name, action, outcome, detail)
	}
}

func formatVideoSeconds(seconds float64) string { return strconv.FormatFloat(seconds, 'f', -1, 64) }

func processCourse(ctx context.Context, client *Client, course Course, speed float64) error {
	logLine("info", "课程「%s」开始处理", course.Name)
	if err := client.UpdateVisits(ctx, course.ID); err != nil {
		if ctx.Err() != nil || KindOf(err) == KindAuthExpired {
			return err
		}
		logLine("warn", "课程「%s」记录访问失败（%s），继续处理", course.Name, Excerpt(err.Error(), 120))
	}
	detail, err := client.CourseDetail(ctx, course.ID)
	if err != nil {
		if ctx.Err() != nil || KindOf(err) == KindAuthExpired {
			return err
		}
		logLine("warn", "课程「%s」获取详情失败（%s），按题目时间估算观看时长", course.Name, Excerpt(err.Error(), 120))
	}
	questions, err := client.ListQuestions(ctx, course.ID)
	if err != nil {
		return err
	}
	duration := CourseTargetSeconds(detail, questions)
	sort.SliceStable(questions, func(i, j int) bool { return questions[i].EjectTime < questions[j].EjectTime })
	for _, question := range questions {
		if float64(question.EjectTime) > duration {
			return newError(KindFormat, fmt.Sprintf("题目弹出位置 %d 秒超出视频时长 %s 秒", question.EjectTime, formatVideoSeconds(duration)))
		}
	}
	logLine("info", "课程「%s」开始播放并上报观看进度，视频时长 %s 秒", course.Name, formatVideoSeconds(duration))
	report := func(seconds float64) error {
		return client.ReportProgressWithResponse(ctx, course.ID, seconds, courseRequestLogger(course, "上报进度", seconds))
	}
	if err := report(0); err != nil {
		return err
	}
	position, nextReport, nextQuestion := 0.0, 10.0, 0
	for {
		if err := ctx.Err(); err != nil {
			return err
		}
		for nextQuestion < len(questions) && float64(questions[nextQuestion].EjectTime) <= position {
			question := questions[nextQuestion]
			logLine("info", "课程「%s」视频到达第 %d 秒，开始答题", course.Name, question.EjectTime)
			if err := client.SubmitAnswerWithResponse(ctx, course.ID, question, courseRequestLogger(course, "答题")); err != nil {
				return err
			}
			nextQuestion++
			if nextQuestion < len(questions) {
				if err := sleepContext(ctx, 120*time.Millisecond); err != nil {
					return err
				}
			}
		}
		if position >= duration {
			break
		}
		next := min(nextReport, duration)
		if nextQuestion < len(questions) {
			next = min(next, float64(questions[nextQuestion].EjectTime))
		}
		if err := sleepContext(ctx, time.Duration((next-position)*float64(time.Second)/speed)); err != nil {
			return err
		}
		position = next
		if nextReport <= position {
			if err := report(nextReport); err != nil {
				return err
			}
			nextReport += 10
		}
	}
	logLine("info", "课程「%s」已播放完整视频时长 %s 秒", course.Name, formatVideoSeconds(duration))
	if err := client.FinishCourseWithResponse(ctx, course.ID, courseRequestLogger(course, "标记完成")); err != nil {
		return err
	}
	logLine("info", "课程「%s」完成，已提交 %d 道题", course.Name, len(questions))
	return nil
}

func runCourses(ctx context.Context, client *Client, pending []Course, speed float64) error {
	ctx, cancel := context.WithCancel(ctx)
	defer cancel()
	jobs := make(chan Course)
	var wg sync.WaitGroup
	var mu sync.Mutex
	var failure error
	for range 4 {
		wg.Go(func() {
			for course := range jobs {
				if ctx.Err() != nil {
					return
				}
				if err := processCourse(ctx, client, course, speed); err != nil {
					mu.Lock()
					if failure == nil || KindOf(err) == KindAuthExpired {
						failure = err
					}
					mu.Unlock()
					logLine("warn", "课程「%s」未完成：%s", course.Name, err)
					if KindOf(err) == KindAuthExpired {
						cancel()
						return
					}
				}
			}
		})
	}
send:
	for _, course := range pending {
		select {
		case jobs <- course:
		case <-ctx.Done():
			break send
		}
	}
	close(jobs)
	wg.Wait()
	if failure != nil && KindOf(failure) == KindAuthExpired {
		return failure
	}
	if ctx.Err() != nil {
		return ctx.Err()
	}
	return nil
}

//go:embed fonts/*.ttf
var bundledFonts embed.FS

const commitmentTemplate = `实验室安全承诺书
我已认真学习了《南京邮电大学实验室安全教育课程》，熟悉实验室各项管理制度和要求。本人承诺今后将严格遵守实验室各项安全制度和操作规程，不断加强实验室安全知识的学习、了解所处实验室周边的应急设施及其正确使用方法、了解所处实验室和所涉实验项目中潜在的危险源、学习相应的防护和应急救援知识，并做好警示和告知工作。如因自己违反规定发生安全事故，造成人身伤害和财产损失，我愿承担相应责任。







所在学院：
学    号：
身份证号：
本人签字：`

func defaultAssets() (*Assets, error) {
	data, err := bundledFonts.ReadFile("fonts/serif-regular.ttf")
	if err != nil {
		return nil, err
	}
	serif, err := opentype.Parse(data)
	if err != nil {
		return nil, err
	}
	assets := &Assets{Serif: serif, Template: ParseTemplate(commitmentTemplate)}
	for _, key := range []string{"chunfeng", "qiuhong", "xingshu"} {
		data, err := bundledFonts.ReadFile("fonts/" + key + ".ttf")
		if err != nil {
			return nil, err
		}
		face, err := opentype.Parse(data)
		if err != nil {
			return nil, err
		}
		assets.Handwriting = append(assets.Handwriting, &Handwriting{Key: key, Name: bundledFontNames[key], Font: face})
	}
	return assets, nil
}

func runDocument(ctx context.Context, client *Client, credentials Credentials, force bool) error {
	info, err := client.QueryMyInfo(ctx)
	if err != nil {
		return err
	}
	if !force && strings.TrimSpace(info.CommitmentPath) != "" {
		logLine("info", "平台上已有承诺书（%s），跳过生成与上传", info.CommitmentPath)
		return nil
	}
	logLine("info", "正在获取个人信息")
	profile, err := FetchProfile(ctx, client.Session, credentials, "")
	if err != nil {
		return err
	}
	if profile.Name == "" {
		profile.Name = info.Name
	}
	if profile.Name == "" || profile.College == "" || !ValidIDNumber(profile.IDNumber) {
		return newError(KindFormat, "个人信息不完整，无法生成承诺书")
	}
	assets, err := defaultAssets()
	if err != nil {
		return err
	}
	fields := Fields{College: profile.College, StudentID: credentials.Username, IDNumber: profile.IDNumber, Name: profile.Name}
	font := assets.ChooseFont(fields, "", uint64(time.Now().UnixNano()))
	result, err := Render(assets, fields, font.Key)
	if err != nil {
		return err
	}
	logLine("info", "承诺书已生成（字体：%s）", result.Font.Name)
	logLine("info", "正在上传承诺书（%d KB，字体 %s）", len(result.JPEG)/1024, result.Font.Name)
	remote, err := client.UploadFile(ctx, time.Now().Format("2006-01-02_15-04-05")+".jpg", result.JPEG, "image/jpeg")
	if err != nil {
		return err
	}
	if err := client.BindCommitment(ctx, remote); err != nil {
		return err
	}
	confirmed, err := client.QueryMyInfo(ctx)
	if err != nil {
		return err
	}
	if strings.TrimSpace(confirmed.CommitmentPath) == "" {
		return newError(KindAPI, "承诺书已上传但平台未记录，稍后重试")
	}
	logLine("info", "承诺书已上传并绑定到账号：%s", confirmed.CommitmentPath)
	return nil
}

func passedExam(definitions []ExamDefinition) *ExamDefinition {
	for _, definition := range definitions {
		if definition.Passed() {
			return &definition
		}
	}
	return nil
}

func runExam(ctx context.Context, client *Client) (bool, error) {
	logLine("info", "正在获取考试列表")
	definitions, err := client.ListExams(ctx)
	if err != nil {
		return false, err
	}
	if passed := passedExam(definitions); passed != nil {
		logLine("info", "考试列表已显示合格（%s，%s 分），无需重复提交", passed.Name, formatVideoSeconds(*passed.Score))
		return true, nil
	}
	var definition *ExamDefinition
	for _, exam := range definitions {
		if exam.Available(time.Now()) {
			definition = &exam
			break
		}
	}
	if definition == nil {
		return false, newError(KindAPI, "当前没有可开始的考试，稍后重新检查")
	}
	logLine("info", "正在处理考试：%s（剩余 %d 次机会）", definition.Name, definition.AttemptLimit-definition.UsedAttempts)
	exam, err := client.StartExam(ctx, *definition)
	if err != nil {
		return false, err
	}
	logLine("info", "已获取 %d 道考题，10 秒后提交答案", len(exam.Questions))
	if err := sleepContext(ctx, 10*time.Second); err != nil {
		return false, err
	}
	result, err := client.SubmitExam(ctx, exam)
	if err != nil {
		return false, err
	}
	confirmed, err := client.ConfirmExamPassed(ctx, *definition, 4)
	if err != nil {
		return false, err
	}
	score := result.Score
	if confirmed.Score != nil {
		score = formatVideoSeconds(*confirmed.Score)
	}
	logLine("info", "考试列表已确认合格，最高分 %s，证书已生成", score)
	return true, nil
}

func runAccount(ctx context.Context, client *Client, credentials Credentials) error {
	firstPassCompleted, coursesCompleted, documentReady := false, false, false
	uploads, failures, passes := 0, 0, 0
	for {
		if err := ctx.Err(); err != nil {
			return err
		}
		definitions, err := client.ListExams(ctx)
		if err == nil && passedExam(definitions) != nil {
			logLine("info", "考试列表已显示合格，无需重复提交")
			return openCertificate(ctx, credentials)
		}
		if err != nil && KindOf(err) != KindAuthExpired && !IsTransient(err) {
			err = nil
		}
		if err == nil && !coursesCompleted {
			logLine("info", "课程「全部课程」正在获取课程列表")
			var courses []Course
			courses, err = client.ListCourses(ctx)
			if err == nil {
				sort.SliceStable(courses, func(i, j int) bool { return courseNameLess(courses[i].Name, courses[j].Name) })
				var pending []Course
				for _, course := range courses {
					if !course.Finished {
						pending = append(pending, course)
					}
				}
				logLine("info", "课程「全部课程」共 %d 门：%d 门已完成，%d 门待处理", len(courses), len(courses)-len(pending), len(pending))
				if len(pending) > 0 {
					if passes >= 2 {
						err = newError(KindAPI, fmt.Sprintf("仍有 %d 门课程未完成", len(pending)))
					} else {
						speed := 2.0
						if firstPassCompleted {
							speed = 1
						}
						passes++
						err = runCourses(ctx, client, pending, speed)
						if err == nil {
							firstPassCompleted = true
							continue
						}
					}
				} else {
					coursesCompleted = true
				}
			}
		}
		if err == nil && !documentReady {
			err = runDocument(ctx, client, credentials, uploads > 0)
			if err == nil {
				documentReady = true
				uploads++
			}
		}
		if err == nil {
			var done bool
			done, err = runExam(ctx, client)
			if err == nil && done {
				return openCertificate(ctx, credentials)
			}
		}
		if ctx.Err() != nil {
			return ctx.Err()
		}
		var pe *Error
		if errors.As(err, &pe) && (pe.Code == "not-qualified" || pe.Code == "unconfirmed") {
			return err
		}
		if KindOf(err) == KindAuthExpired {
			logLine("warn", "登录状态失效，正在重新登录")
			fresh, ssoOK, loginErr := loginPlatform(ctx, credentials)
			if loginErr == nil {
				client = fresh
				continue
			}
			if !ssoOK {
				fmt.Printf("登录SSO失败：%s\n", loginErr)
			}
			err = loginErr
		}
		if err != nil && wantsAnotherUpload(err) && uploads < 3 {
			documentReady = false
		}
		if err != nil && (KindOf(err) == KindFormat || KindOf(err) == KindAuth) {
			return err
		}
		delay := time.Duration(min(30*(1<<min(failures, 4)), 300)) * time.Second
		if err != nil && looksLikeReviewPending(err) {
			delay = 10 * time.Minute
		}
		logLine("warn", "本次尝试失败：%s；%s 后自动重试", err, delay)
		if err := sleepContext(ctx, delay); err != nil {
			return err
		}
		failures++
		passes = 0
	}
}

var reviewPendingPattern = regexp.MustCompile(`授权|承诺书|审核|审批|资格|未通过|请先上传`)

var reuploadPattern = regexp.MustCompile(`未通过|驳回|不通过|重新上传|请先上传|未上传`)

func looksLikeReviewPending(err error) bool {
	return KindOf(err) == KindAPI && !IsTransient(err) && reviewPendingPattern.MatchString(err.Error())
}

func wantsAnotherUpload(err error) bool { return reuploadPattern.MatchString(err.Error()) }

func openCertificate(ctx context.Context, credentials Credentials) error {
	s := NewSession(nil)
	s.SetAccount(credentials.Username)
	ticket, err := serviceTicket(ctx, s, credentials)
	if err != nil {
		return err
	}
	target := IntranetOrigin + "/students/cert?ticket=" + url.QueryEscape(ticket) + "&service=http%3A%2F%2F10.22.192.38%3A9092"
	verb, _ := windows.UTF16PtrFromString("open")
	address, _ := windows.UTF16PtrFromString(target)
	result, _, callErr := windows.NewLazySystemDLL("shell32.dll").NewProc("ShellExecuteW").Call(0, uintptr(unsafe.Pointer(verb)), uintptr(unsafe.Pointer(address)), 0, 0, 1)
	if result <= 32 {
		return fmt.Errorf("打开证书页面失败：%v", callErr)
	}
	logLine("info", "任务完成")
	return nil
}

func main() {
	name, _ := windows.UTF16PtrFromString(`Global\linkium-lab-helper`)
	mutex, err := windows.CreateMutex(nil, false, name)
	if errors.Is(err, windows.ERROR_ALREADY_EXISTS) {
		if mutex != 0 {
			windows.CloseHandle(mutex)
		}
		return
	}
	if err != nil {
		return
	}
	defer windows.CloseHandle(mutex)
	title, _ := windows.UTF16PtrFromString("联创实验室助手")
	windows.NewLazySystemDLL("kernel32.dll").NewProc("SetConsoleTitleW").Call(uintptr(unsafe.Pointer(title)))
	windows.NewLazySystemDLL("kernel32.dll").NewProc("SetConsoleCP").Call(65001)
	windows.NewLazySystemDLL("kernel32.dll").NewProc("SetConsoleOutputCP").Call(65001)
	fmt.Printf("联创实验室助手 v%s\n", version)
	fmt.Println("获取更多南邮校内课程资源，请访问 https://xinzhires.mtszedu.com")
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt)
	defer stop()
	reader := bufio.NewReader(os.Stdin)
	read := func(prompt string) (string, error) {
		fmt.Println(prompt)
		text, err := reader.ReadString('\n')
		if err != nil && (err != io.EOF || len(text) == 0) {
			return "", err
		}
		return strings.TrimSuffix(strings.TrimSuffix(text, "\n"), "\r"), nil
	}
	for {
		username, err := read("请输入学号：")
		if err != nil {
			return
		}
		password, err := read("请输入密码：")
		if err != nil {
			return
		}
		credentials := Credentials{Username: strings.TrimSpace(username), Password: password}
		client, ssoOK, err := loginPlatform(ctx, credentials)
		if err != nil {
			if ctx.Err() != nil {
				return
			}
			if ssoOK {
				fmt.Printf("登录实验室系统失败：%s\n", err)
			} else {
				fmt.Printf("登录SSO失败：%s\n", err)
			}
			continue
		}
		if err := runAccount(ctx, client, credentials); err != nil && ctx.Err() == nil {
			logLine("error", "%s", err)
		}
		return
	}
}
