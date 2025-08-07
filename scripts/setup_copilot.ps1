Write-Host "🚀 Setting up GitHub Copilot for Lean 4 project..." -ForegroundColor Green

# Install required VS Code extensions
$extensions = @(
    "github.copilot",
    "github.copilot-chat",
    "leanprover.lean4"
)

foreach ($ext in $extensions) {
    Write-Host "Installing $ext..." -ForegroundColor Cyan
    code --install-extension $ext
}

# Create workspace settings
$workspaceSettings = @{
    "github.copilot.enable" = @{
        "*" = $true
        "lean4" = $true
        "markdown" = $true
    }
    "lean4.toolchain" = "leanprover/lean4:v4.2.0"
    "lean4.server.maxPendingRequestsPerReference" = 20
}

$settingsPath = ".vscode/settings.json"
New-Item -ItemType Directory -Force -Path ".vscode"
$workspaceSettings | ConvertTo-Json -Depth 3 | Set-Content $settingsPath

Write-Host "✅ Setup complete!" -ForegroundColor Green
Write-Host "🔄 Restart VS Code to apply changes" -ForegroundColor Yellow
Write-Host "💡 Use Ctrl+Shift+I to open Copilot chat" -ForegroundColor Cyan
