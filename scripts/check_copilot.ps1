Write-Host "🔍 Checking GitHub Copilot Configuration..." -ForegroundColor Green

# Check if GitHub CLI is installed
try {
    $ghVersion = gh --version 2>$null
    Write-Host "✅ GitHub CLI installed: $($ghVersion[0])" -ForegroundColor Green
} catch {
    Write-Host "❌ GitHub CLI not found" -ForegroundColor Red
    Write-Host "💡 Install from: https://cli.github.com/" -ForegroundColor Yellow
}

# Check VS Code extensions
Write-Host "`n📦 Checking VS Code Extensions..." -ForegroundColor Cyan

$extensions = @(
    "github.copilot",
    "github.copilot-chat", 
    "ms-vscode.vscode-json",
    "ms-python.python"
)

foreach ($ext in $extensions) {
    try {
        $result = code --list-extensions | Select-String $ext
        if ($result) {
            Write-Host "✅ $ext installed" -ForegroundColor Green
        } else {
            Write-Host "❌ $ext not found" -ForegroundColor Red
            Write-Host "💡 Install with: code --install-extension $ext" -ForegroundColor Yellow
        }
    } catch {
        Write-Host "⚠️  Could not check extensions" -ForegroundColor Yellow
    }
}

# Check Copilot status
Write-Host "`n🤖 GitHub Copilot Commands in VS Code:" -ForegroundColor Cyan
Write-Host "• Ctrl+I        - Inline chat" -ForegroundColor White
Write-Host "• Ctrl+Shift+I  - Chat panel" -ForegroundColor White  
Write-Host "• @workspace    - Ask about workspace" -ForegroundColor White
Write-Host "• /explain      - Explain code" -ForegroundColor White
Write-Host "• /fix          - Fix problems" -ForegroundColor White
Write-Host "• /tests        - Generate tests" -ForegroundColor White

Write-Host "`n⚙️  VS Code Settings to Configure:" -ForegroundColor Cyan
Write-Host "• File > Preferences > Settings" -ForegroundColor White
Write-Host "• Search 'copilot'" -ForegroundColor White
Write-Host "• Enable suggestions, chat, etc." -ForegroundColor White
