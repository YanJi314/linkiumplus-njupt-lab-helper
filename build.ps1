$ErrorActionPreference = "Stop"
Push-Location $PSScriptRoot
try {
    $version = (Get-Content -LiteralPath VERSION -Raw).Trim()
    go build -trimpath -ldflags "-X main.version=$version" -o linkium-lab-helper.exe main.go
    if ($LASTEXITCODE -ne 0) { throw "Build failed" }
} finally {
    Pop-Location
}
