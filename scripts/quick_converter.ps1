param(
    [string]$OutputDir = "C:\Users\Moses\math_ops\OperatorKernelO6\Docs"
)

Write-Host "=== QUICK FILE CONVERTER ===" -ForegroundColor Cyan
Write-Host "Simple, fast file conversion for your most common tasks" -ForegroundColor Green
Write-Host ""

# Easy configuration - MODIFY THESE PATHS AT THE TOP!
$DIRS = @{
    "1" = @{ Name = "Core Docs"; Path = "C:\Users\Moses\math_ops\OperatorKernelO6\Core_Docs"; Pattern = "*.md" }
    "2" = @{ Name = "Lean Source"; Path = "C:\Users\Moses\math_ops\OperatorKernelO6\OperatorKernelO6"; Pattern = "*.lean" }
    "3" = @{ Name = "Lean Meta"; Path = "C:\Users\Moses\math_ops\OperatorKernelO6\OperatorKernelO6\Meta"; Pattern = "*.lean" }
    "4" = @{ Name = "All Docs"; Path = "C:\Users\Moses\math_ops\OperatorKernelO6\Docs"; Pattern = "*.md" }
}

# Quick combos - MODIFY THESE PRESETS!
$COMBOS = @{
    "A" = @{ Name = "Core Theory"; Files = @("Core_Docs\Operator Centric Foundations of Godelian Incompleteness.md", "Core_Docs\Termination_Companion.md") }
    "B" = @{ Name = "Meta Files"; Files = @("OperatorKernelO6\Meta\Godel.lean", "OperatorKernelO6\Meta\Normalize.lean") }
    "C" = @{ Name = "Main Kernel"; Files = @("OperatorKernelO6\Kernel.lean", "OperatorKernelO6\Meta\Godel.lean") }
}

Write-Host "QUICK OPTIONS:" -ForegroundColor Yellow
Write-Host "  [A] Core Theory (Foundations + Termination)" -ForegroundColor White  
Write-Host "  [B] Meta Files (Godel + Normalize)" -ForegroundColor White
Write-Host "  [C] Main Kernel (Kernel + Godel)" -ForegroundColor White
Write-Host ""

Write-Host "DIRECTORY OPTIONS:" -ForegroundColor Yellow
foreach ($key in $DIRS.Keys | Sort-Object) {
    $dir = $DIRS[$key]
    $exists = Test-Path $dir.Path
    $status = if ($exists) { "OK" } else { "MISSING" }
    Write-Host "  [$key] $status $($dir.Name) -> $($dir.Path)" -ForegroundColor White
}
Write-Host ""

$choice = Read-Host "Choose quick combo (A,B,C) or directory (1,2,3,4) or ENTER for custom"

$filesToProcess = @()
$customTitle = ""

# Handle choice
switch ($choice.ToUpper()) {
    "A" {
        $combo = $COMBOS["A"]
        $customTitle = $combo.Name
        foreach ($file in $combo.Files) {
            $fullPath = "C:\Users\Moses\math_ops\OperatorKernelO6\$file"
            if (Test-Path $fullPath) {
                $filesToProcess += @{
                    Path = $fullPath
                    Name = [System.IO.Path]::GetFileNameWithoutExtension($fullPath)
                    Type = if ($fullPath -like "*.md") { "markdown" } else { "lean" }
                    Description = "From $file"
                }
            }
        }
    }
    "B" {
        $combo = $COMBOS["B"]
        $customTitle = $combo.Name
        foreach ($file in $combo.Files) {
            $fullPath = "C:\Users\Moses\math_ops\OperatorKernelO6\$file"
            if (Test-Path $fullPath) {
                $filesToProcess += @{
                    Path = $fullPath
                    Name = [System.IO.Path]::GetFileNameWithoutExtension($fullPath)
                    Type = if ($fullPath -like "*.md") { "markdown" } else { "lean" }
                    Description = "From $file"
                }
            }
        }
    }
    "C" {
        $combo = $COMBOS["C"]
        $customTitle = $combo.Name
        foreach ($file in $combo.Files) {
            $fullPath = "C:\Users\Moses\math_ops\OperatorKernelO6\$file"
            if (Test-Path $fullPath) {
                $filesToProcess += @{
                    Path = $fullPath
                    Name = [System.IO.Path]::GetFileNameWithoutExtension($fullPath)
                    Type = if ($fullPath -like "*.md") { "markdown" } else { "lean" }
                    Description = "From $file"
                }
            }
        }
    }
    { $_ -in @("1","2","3","4") } {
        $dir = $DIRS[$choice]
        $customTitle = "$($dir.Name)_Files"
        if (Test-Path $dir.Path) {
            Get-ChildItem -Path $dir.Path -Filter $dir.Pattern -Recurse | ForEach-Object {
                $filesToProcess += @{
                    Path = $_.FullName
                    Name = $_.BaseName
                    Type = if ($_.Extension -eq ".md") { "markdown" } else { "lean" }
                    Description = "From $($dir.Name)"
                }
            }
        }
    }
    default {
        Write-Host "Custom selection - showing all available files..." -ForegroundColor Yellow
        $allFiles = @()
        foreach ($key in $DIRS.Keys) {
            $dir = $DIRS[$key]
            if (Test-Path $dir.Path) {
                Get-ChildItem -Path $dir.Path -Filter $dir.Pattern -Recurse | ForEach-Object {
                    $allFiles += @{
                        Path = $_.FullName
                        Name = $_.BaseName
                        Type = if ($_.Extension -eq ".md") { "markdown" } else { "lean" }
                        Description = "From $($dir.Name)"
                        DisplayName = "$($_.BaseName)$($_.Extension) [$($dir.Name)]"
                    }
                }
            }
        }
        
        Write-Host ""
        Write-Host "AVAILABLE FILES:" -ForegroundColor Green
        for ($i = 0; $i -lt $allFiles.Count; $i++) {
            Write-Host "  [$($i + 1)] $($allFiles[$i].DisplayName)" -ForegroundColor White
        }
        
        Write-Host ""
        $selection = Read-Host "Enter file numbers (e.g., 1,3,5) or 'all'"
        
        if ($selection.ToLower() -eq 'all') {
            $filesToProcess = $allFiles
        } else {
            $numbers = $selection.Split(',') | ForEach-Object { $_.Trim() }
            foreach ($num in $numbers) {
                if ($num -match '^\d+$' -and [int]$num -le $allFiles.Count -and [int]$num -gt 0) {
                    $filesToProcess += $allFiles[[int]$num - 1]
                }
            }
        }
        $customTitle = "Custom_Selection"
    }
}

if ($filesToProcess.Count -eq 0) {
    Write-Host "No files found to process!" -ForegroundColor Red
    exit
}

Write-Host ""
Write-Host "PROCESSING FILES:" -ForegroundColor Cyan
foreach ($file in $filesToProcess) {
    Write-Host "  • $($file.Name) ($($file.Type))" -ForegroundColor Gray
}

Write-Host ""
Write-Host "Converting to HTML and PDF..." -ForegroundColor Green

# Create output directory
New-Item -ItemType Directory -Path $OutputDir -Force | Out-Null

# Load System.Web for HTML encoding
Add-Type -AssemblyName System.Web

# Simple HTML generation function
function Generate-SimpleHtml {
    param([string]$Title, [string]$Content, [string]$Type)
    
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    
    if ($Type -eq "markdown") {
        # Basic markdown to HTML
        $htmlContent = $Content
        $htmlContent = $htmlContent -replace '(?m)^### (.*)', '<h3>$1</h3>'
        $htmlContent = $htmlContent -replace '(?m)^## (.*)', '<h2>$1</h2>'
        $htmlContent = $htmlContent -replace '(?m)^# (.*)', '<h1>$1</h1>'
        $htmlContent = $htmlContent -replace '\*\*(.*?)\*\*', '<strong>$1</strong>'
        $htmlContent = $htmlContent -replace '\*(.*?)\*', '<em>$1</em>'
        $htmlContent = $htmlContent -replace '`([^`]+)`', '<code>$1</code>'
        $htmlContent = $htmlContent -replace '(?m)\n\n', '</p><p>'
        $htmlContent = "<div>$htmlContent</div>"
    } else {
        $htmlContent = "<pre><code>" + [System.Web.HttpUtility]::HtmlEncode($Content) + "</code></pre>"
    }

return @"
<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>$Title</title>
    <style>
        body { max-width: 1000px; margin: 0 auto; padding: 20px; font-family: system-ui, sans-serif; }
        h1 { color: #2c3e50; border-bottom: 2px solid #3498db; padding-bottom: 10px; }
        h2 { color: #34495e; margin-top: 30px; }
        pre { background: #f8f9fa; padding: 15px; border-radius: 5px; overflow-x: auto; }
        code { font-family: 'Consolas', monospace; }
        .meta { background: #e8f4fd; padding: 15px; border-radius: 5px; margin: 20px 0; }
    </style>
</head>
<body>
    <h1>$Title</h1>
    <div class="meta">Generated: $timestamp | Type: $Type</div>
    $htmlContent
</body>
</html>
"@
}

# Process each file
$processedFiles = @()
foreach ($file in $filesToProcess) {
    try {
        $content = Get-Content $file.Path -Raw -Encoding UTF8
        if ([string]::IsNullOrWhiteSpace($content)) {
            $content = "-- File appears to be empty"
        }
        
        $safeName = $file.Name -replace '[^\w\-_]', '_'
        $htmlFile = Join-Path $OutputDir "$safeName.html"
        
        $html = Generate-SimpleHtml -Title $file.Name -Content $content -Type $file.Type
        $html | Out-File -FilePath $htmlFile -Encoding UTF8
        
        Write-Host "✓ Created: $safeName.html" -ForegroundColor Green
        
        $processedFiles += @{
            Name = $file.Name
            Content = $content
            Type = $file.Type
            Description = $file.Description
        }
    } catch {
        Write-Host "✗ Failed: $($file.Name) - $($_.Exception.Message)" -ForegroundColor Red
    }
}

# Create combined document if multiple files
if ($processedFiles.Count -gt 1) {
    Write-Host ""
    Write-Host "Creating combined document..." -ForegroundColor Cyan
    
    $combinedContent = "# $customTitle`n`nCombined document with $($processedFiles.Count) files.`n`n"
    
    foreach ($file in $processedFiles) {
        $combinedContent += "## $($file.Name)`n`n"
        if ($file.Description) {
            $combinedContent += "*$($file.Description)*`n`n"
        }
        $combinedContent += "``````$($file.Type)`n"
        $combinedContent += $file.Content
        $combinedContent += "`n``````n`n---`n`n"
    }
    
    $safeCombinedTitle = $customTitle -replace '[^\w\-_]', '_'
    $combinedHtmlFile = Join-Path $OutputDir "$safeCombinedTitle.html"
    
    $combinedHtml = Generate-SimpleHtml -Title $customTitle -Content $combinedContent -Type "markdown"
    $combinedHtml | Out-File -FilePath $combinedHtmlFile -Encoding UTF8
    
    Write-Host "✓ Created combined: $safeCombinedTitle.html" -ForegroundColor Green
}

Write-Host ""
Write-Host "CONVERSION COMPLETE!" -ForegroundColor Green
Write-Host "Files saved to: $OutputDir" -ForegroundColor White
Write-Host "Individual files: $($processedFiles.Count)" -ForegroundColor Gray
if ($processedFiles.Count -gt 1) {
    Write-Host "Combined document: $customTitle" -ForegroundColor Gray
}

Write-Host ""
Write-Host "TIP: Edit the DIRS and COMBOS hashtables at the top of this script to customize your options!" -ForegroundColor Yellow