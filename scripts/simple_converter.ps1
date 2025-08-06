param(
    [string]$OutputDir = "C:\Users\Moses\math_ops\OperatorKernelO6\Docs"
)

Write-Host "=== SIMPLE FILE CONVERTER ===" -ForegroundColor Cyan
Write-Host ""

# EASY CONFIGURATION - MODIFY THESE PATHS:
$PRESETS = @{
    "1" = @{ 
        Name = "Core Theory Docs"
        Files = @(
            "C:\Users\Moses\math_ops\OperatorKernelO6\Core_Docs\Operator Centric Foundations of Godelian Incompleteness.md",
            "C:\Users\Moses\math_ops\OperatorKernelO6\Core_Docs\Termination_Companion.md"
        )
    }
    "2" = @{
        Name = "Meta Lean Files" 
        Files = @(
            "C:\Users\Moses\math_ops\OperatorKernelO6\OperatorKernelO6\Meta\Godel.lean",
            "C:\Users\Moses\math_ops\OperatorKernelO6\OperatorKernelO6\Meta\Normalize.lean"
        )
    }
    "3" = @{
        Name = "Core + Godel"
        Files = @(
            "C:\Users\Moses\math_ops\OperatorKernelO6\Core_Docs\Operator Centric Foundations of Godelian Incompleteness.md",
            "C:\Users\Moses\math_ops\OperatorKernelO6\OperatorKernelO6\Meta\Godel.lean"
        )
    }
}

Write-Host "PRESET OPTIONS:" -ForegroundColor Yellow
Write-Host "  [1] Core Theory Docs (Foundations + Termination)" -ForegroundColor White
Write-Host "  [2] Meta Lean Files (Godel + Normalize)" -ForegroundColor White  
Write-Host "  [3] Core + Godel (Mixed content)" -ForegroundColor White
Write-Host "  [C] Custom file paths (you specify)" -ForegroundColor White
Write-Host ""

$choice = Read-Host "Choose option (1, 2, 3, or C)"

$filesToProcess = @()
$title = "Custom_Conversion"

if ($choice -eq "C" -or $choice -eq "c") {
    Write-Host ""
    Write-Host "Enter full file paths, one per line. Press Enter twice when done:" -ForegroundColor Green
    $customFiles = @()
    do {
        $path = Read-Host "File path"
        if ($path -and (Test-Path $path)) {
            $customFiles += $path
            Write-Host "  Added: $path" -ForegroundColor Gray
        } elseif ($path) {
            Write-Host "  File not found: $path" -ForegroundColor Red
        }
    } while ($path)
    
    foreach ($path in $customFiles) {
        $filesToProcess += @{
            Path = $path
            Name = [System.IO.Path]::GetFileNameWithoutExtension($path)
            Type = if ($path -like "*.md") { "markdown" } else { "lean" }
        }
    }
    $title = "Custom_Files"
} elseif ($PRESETS.ContainsKey($choice)) {
    $preset = $PRESETS[$choice]
    $title = $preset.Name -replace '\s+', '_'
    
    foreach ($path in $preset.Files) {
        if (Test-Path $path) {
            $filesToProcess += @{
                Path = $path
                Name = [System.IO.Path]::GetFileNameWithoutExtension($path)
                Type = if ($path -like "*.md") { "markdown" } else { "lean" }
            }
            Write-Host "Found: $([System.IO.Path]::GetFileName($path))" -ForegroundColor Green
        } else {
            Write-Host "Missing: $([System.IO.Path]::GetFileName($path))" -ForegroundColor Red
        }
    }
} else {
    Write-Host "Invalid choice!" -ForegroundColor Red
    exit
}

if ($filesToProcess.Count -eq 0) {
    Write-Host "No files to process!" -ForegroundColor Red
    exit
}

Write-Host ""
Write-Host "Processing $($filesToProcess.Count) files..." -ForegroundColor Cyan

# Create output directory
New-Item -ItemType Directory -Path $OutputDir -Force | Out-Null
Add-Type -AssemblyName System.Web

# Simple HTML template
function Create-HTML {
    param([string]$Title, [string]$Content, [string]$Type)
    
    $escapedContent = if ($Type -eq "markdown") {
        # Basic markdown conversion
        $html = $Content
        $html = $html -replace '(?m)^## (.*)', '<h2>$1</h2>'
        $html = $html -replace '(?m)^# (.*)', '<h1>$1</h1>'
        $html = $html -replace '\*\*(.*?)\*\*', '<strong>$1</strong>'
        $html = $html -replace '\*(.*?)\*', '<em>$1</em>'
        $html = $html -replace '(?m)\n\n', '</p><p>'
        "<div><p>$html</p></div>"
    } else {
        "<pre><code>" + [System.Web.HttpUtility]::HtmlEncode($Content) + "</code></pre>"
    }

    return @"
<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>$Title</title>
    <style>
        body { max-width: 1000px; margin: 0 auto; padding: 20px; font-family: Arial, sans-serif; }
        h1 { color: #2c3e50; border-bottom: 2px solid #3498db; padding-bottom: 10px; }
        h2 { color: #34495e; }
        pre { background: #f8f9fa; padding: 15px; border-radius: 5px; overflow-x: auto; }
        code { font-family: Consolas, monospace; }
    </style>
</head>
<body>
    <h1>$Title</h1>
    $escapedContent
</body>
</html>
"@
}

# Process files
$processedContent = ""
foreach ($file in $filesToProcess) {
    Write-Host "Processing: $($file.Name)" -ForegroundColor White
    
    $content = Get-Content $file.Path -Raw -Encoding UTF8
    $safeName = $file.Name -replace '[^\w\-_]', '_'
    
    # Create individual HTML file
    $html = Create-HTML -Title $file.Name -Content $content -Type $file.Type
    $htmlPath = Join-Path $OutputDir "$safeName.html"
    $html | Out-File -FilePath $htmlPath -Encoding UTF8
    Write-Host "  Created: $safeName.html" -ForegroundColor Green
    
    # Add to combined content
    $processedContent += "`n`n## $($file.Name)`n`n"
    $processedContent += "``````$($file.Type)`n$content`n```````n"
}

# Create combined file
if ($filesToProcess.Count -gt 1) {
    $combinedTitle = $title + "_Combined"
    $combinedContent = "# $combinedTitle`n`nCombined document with all selected files:`n$processedContent"
    $combinedHtml = Create-HTML -Title $combinedTitle -Content $combinedContent -Type "markdown"
    $combinedPath = Join-Path $OutputDir "$combinedTitle.html"
    $combinedHtml | Out-File -FilePath $combinedPath -Encoding UTF8
    Write-Host ""
    Write-Host "Created combined: $combinedTitle.html" -ForegroundColor Green
}

Write-Host ""
Write-Host "COMPLETE! Files saved to: $OutputDir" -ForegroundColor Green
Write-Host "Total files processed: $($filesToProcess.Count)" -ForegroundColor White