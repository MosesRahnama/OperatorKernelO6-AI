param(
    [string]$OutputDir = "c:\Users\Moses\math_ops\OperatorKernelO6\docs"
)

Write-Host "=== 🎯 Pick & Convert - YOUR WAY! ===" -ForegroundColor Cyan
Write-Host ""

# Find all available files
$AllFiles = @()

# Scan for .lean files
Get-ChildItem -Path "C:\Users\Moses\math_ops\OperatorKernelO6\OperatorKernelO6" -Filter "*.lean" -Recurse | ForEach-Object {
    $AllFiles += @{
        Path = $_.FullName
        Name = $_.BaseName
        Type = "lean"
        DisplayName = "[$($_.BaseName).lean] - Lean code"
        Description = "Lean source file"
    }
}

# Scan for .md files in core_docs
Get-ChildItem -Path "C:\Users\Moses\math_ops\OperatorKernelO6\core_docs" -Filter "*.md" | ForEach-Object {
    $AllFiles += @{
        Path = $_.FullName
        Name = $_.BaseName
        Type = "markdown"
        DisplayName = "[$($_.BaseName).md] - Documentation"
        Description = "Markdown documentation"
    }
}

# Display all available files
Write-Host "🗂️ Available Files:" -ForegroundColor Yellow
for ($i = 0; $i -lt $AllFiles.Count; $i++) {
    Write-Host "  [$($i + 1)] $($AllFiles[$i].DisplayName)" -ForegroundColor White
}

Write-Host ""
Write-Host "✨ Pick your files! Enter numbers separated by commas or spaces:" -ForegroundColor Green
Write-Host "   Example: 1,3,5 or 1 3 5" -ForegroundColor Gray
$selection = Read-Host "Your selection"

# Parse selection
$selectedNumbers = @()
if ($selection -match ',') {
    $selectedNumbers = $selection.Split(',') | ForEach-Object { $_.Trim() }
} else {
    $selectedNumbers = $selection.Split(' ') | Where-Object { $_ -ne '' } | ForEach-Object { $_.Trim() }
}

# Get selected files
$SelectedFiles = @()
foreach ($num in $selectedNumbers) {
    if ($num -match '^\d+$' -and [int]$num -le $AllFiles.Count -and [int]$num -gt 0) {
        $SelectedFiles += $AllFiles[[int]$num - 1]
    }
}

if ($SelectedFiles.Count -eq 0) {
    Write-Host "❌ No valid files selected. Exiting." -ForegroundColor Red
    exit
}

Write-Host ""
Write-Host "📋 You selected:" -ForegroundColor Green
for ($i = 0; $i -lt $SelectedFiles.Count; $i++) {
    Write-Host "  [$($i + 1)] $($SelectedFiles[$i].DisplayName)" -ForegroundColor Gray
}

Write-Host ""
Write-Host "🔄 Want to reorder them? (y/n):" -ForegroundColor Yellow
$reorder = Read-Host

if ($reorder -eq 'y' -or $reorder -eq 'Y') {
    Write-Host ""
    Write-Host "📐 Current order:" -ForegroundColor Yellow
    for ($i = 0; $i -lt $SelectedFiles.Count; $i++) {
        Write-Host "  [$($i + 1)] $($SelectedFiles[$i].DisplayName)" -ForegroundColor White
    }
    
    Write-Host ""
    Write-Host "✨ Enter new order (e.g., 2,1,3 puts second file first):" -ForegroundColor Green
    $newOrder = Read-Host "New order"
    
    $orderNumbers = $newOrder.Split(',') | ForEach-Object { $_.Trim() }
    $ReorderedFiles = @()
    
    foreach ($num in $orderNumbers) {
        if ($num -match '^\d+$' -and [int]$num -le $SelectedFiles.Count -and [int]$num -gt 0) {
            $ReorderedFiles += $SelectedFiles[[int]$num - 1]
        }
    }
    
    if ($ReorderedFiles.Count -eq $SelectedFiles.Count) {
        $SelectedFiles = $ReorderedFiles
        Write-Host ""
        Write-Host "✅ Reordered to:" -ForegroundColor Green
        for ($i = 0; $i -lt $SelectedFiles.Count; $i++) {
            Write-Host "  [$($i + 1)] $($SelectedFiles[$i].DisplayName)" -ForegroundColor Gray
        }
    } else {
        Write-Host "⚠️ Invalid reorder. Using original order." -ForegroundColor Yellow
    }
}

Write-Host ""
Write-Host "📝 Custom title for combined document:" -ForegroundColor Yellow
$customTitle = Read-Host "Title (or press Enter for default)"
if ($customTitle -eq "") {
    $customTitle = "Custom_Selected_Documentation"
}

Write-Host ""
Write-Host "🚀 Converting your selected files..." -ForegroundColor Cyan

# Create output directory
New-Item -ItemType Directory -Path $OutputDir -Force | Out-Null

# Load System.Web for HTML encoding
Add-Type -AssemblyName System.Web

# Function to convert HTML to PDF (reuse from convert_all_docs.ps1)
function Convert-HtmlToPdf {
    param([string]$HtmlPath, [string]$PdfPath)
    
    $wkhtmltopdf = $null
    $possiblePaths = @(
        "wkhtmltopdf",
        "C:\Program Files\wkhtmltopdf\bin\wkhtmltopdf.exe",
        "C:\Program Files (x86)\wkhtmltopdf\bin\wkhtmltopdf.exe",
        "$env:LOCALAPPDATA\Programs\wkhtmltopdf\bin\wkhtmltopdf.exe"
    )
    
    foreach ($path in $possiblePaths) {
        if (Get-Command $path -ErrorAction SilentlyContinue) {
            $wkhtmltopdf = $path
            break
        }
        if (Test-Path $path) {
            $wkhtmltopdf = $path
            break
        }
    }
    
    if ($wkhtmltopdf) {
        try {
            & $wkhtmltopdf --page-size A4 --margin-top 0.5in --margin-bottom 0.5in --margin-left 0.5in --margin-right 0.5in --enable-local-file-access --print-media-type "$HtmlPath" "$PdfPath" 2>$null
            return $true
        } catch {
            return $false
        }
    }
    return $false
}

# Function to generate HTML content (reuse from convert_all_docs.ps1)
function Generate-HtmlContent {
    param(
        [string]$Title,
        [string]$Content,
        [string]$Description = "",
        [string]$FilePath = "",
        [string]$FileType = "lean"
    )
    
    $Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    
    if ($FileType -eq "markdown") {
        # Simple markdown to HTML conversion
        $htmlContent = $Content
        $htmlContent = $htmlContent -replace '(?m)^### (.*)', '<h3>$1</h3>'
        $htmlContent = $htmlContent -replace '(?m)^## (.*)', '<h2>$1</h2>'
        $htmlContent = $htmlContent -replace '(?m)^# (.*)', '<h1>$1</h1>'
        $htmlContent = $htmlContent -replace '\*\*(.*?)\*\*', '<strong>$1</strong>'
        $htmlContent = $htmlContent -replace '\*(.*?)\*', '<em>$1</em>'
        $htmlContent = $htmlContent -replace '(?s)```(\w+)?\s*\n(.*?)\n```', '<pre><code class="$1">$2</code></pre>'
        $htmlContent = $htmlContent -replace '`([^`]+)`', '<code>$1</code>'
        $htmlContent = $htmlContent -replace '\[([^\]]+)\]\(([^)]+)\)', '<a href="$2">$1</a>'
        $htmlContent = $htmlContent -replace '(?m)\n\n', '</p><p>'
        $htmlContent = "<p>$htmlContent</p>"
        $htmlContent = $htmlContent -replace '<p></p>', ''
        $ContentSection = "<div class='markdown-content'>$htmlContent</div>"
    } else {
        $EscapedContent = [System.Web.HttpUtility]::HtmlEncode($Content)
        $ContentSection = "<pre><code class='lean'>$EscapedContent</code></pre>"
    }
    
    return @"
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>$Title - OperatorKernelO6</title>
    <style>
        body {
            width: 100vw;
            max-width: none;
            margin: 0;
            padding: 20px;
            font-size: 18px;
            color: #333;
            background: #fff;
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
        }
        
        h1 { color: #2c3e50; border-bottom: 3px solid #3498db; padding-bottom: 10px; margin-bottom: 30px; }
        h2 { color: #34495e; border-bottom: 1px solid #bdc3c7; margin-top: 40px; padding-bottom: 5px; }
        
        .metadata {
            background: #e8f4fd; padding: 15px; border-radius: 8px;
            border-left: 4px solid #3498db; margin: 20px 0;
        }
        
        .description {
            background: #f0f8f0; padding: 15px; border-radius: 8px;
            border-left: 4px solid #27ae60; margin: 20px 0;
        }
        
        pre {
            background: #f8f9fa; padding: 20px; border-radius: 8px; overflow-x: auto;
            border: 1px solid #dee2e6; font-size: 14px; line-height: 1.4;
            white-space: pre-wrap; word-wrap: break-word;
            font-family: 'Consolas', 'Monaco', 'Courier New', monospace;
        }
        
        .markdown-content h1, .markdown-content h2, .markdown-content h3 {
            color: #2c3e50; margin-top: 30px; margin-bottom: 15px;
        }
        .markdown-content h1 { border-bottom: 2px solid #3498db; padding-bottom: 10px; }
        .markdown-content h2 { border-bottom: 1px solid #bdc3c7; padding-bottom: 5px; }
        .markdown-content p { margin-bottom: 15px; line-height: 1.6; }
        .markdown-content code {
            background: #f1f2f6; padding: 2px 6px; border-radius: 3px;
            font-family: 'Consolas', 'Monaco', 'Courier New', monospace; font-size: 0.9em;
        }
        
        @media print {
            body { width: 100%; max-width: none; margin: 0; padding: 15px; font-size: 16px; }
            pre { font-size: 13px; line-height: 1.35; margin: 15px 0; padding: 15px;
                  background: #f8f9fa !important; border: 1px solid #dee2e6 !important;
                  width: 100%; box-sizing: border-box; }
            h1 { font-size: 24px; margin-bottom: 20px; }
            h2 { font-size: 20px; margin-top: 25px; }
            .metadata, .description { margin: 15px 0; padding: 12px; }
        }
        
        @page { margin: 0.5in; size: letter; }
    </style>
</head>
<body>
    <h1>$Title</h1>
    
    <div class="metadata">
        <p>
            <strong>File:</strong> <code>$FilePath</code><br>
            <strong>Type:</strong> $FileType<br>
            <strong>Generated:</strong> $Timestamp<br>
            <strong>Size:</strong> $($Content.Length) characters
        </p>
    </div>
    
    $(if ($Description) { "<div class='description'><h3>Overview</h3><p>$Description</p></div>" })
    
    $(if ($FileType -eq "markdown") { "<h2>Document Content</h2>" } else { "<h2>Source Code</h2>" })
    $ContentSection
    
    <script>
        document.addEventListener('DOMContentLoaded', function() {
            const codeElements = document.querySelectorAll('pre code.lean');
            codeElements.forEach(function(codeElement) {
                let content = codeElement.innerHTML;
                
                const keywords = [
                    'import', 'namespace', 'end', 'theorem', 'lemma', 'def', 'noncomputable',
                    'by', 'have', 'exact', 'simpa', 'simp', 'calc', 'cases', 'with',
                    'intro', 'apply', 'rw', 'sorry', 'private', 'open', 'universe',
                    'set_option', 'attribute', 'inductive', 'structure', 'class', 'instance'
                ];
                
                keywords.forEach(keyword => {
                    const regex = new RegExp('\\b' + keyword + '\\b', 'g');
                    content = content.replace(regex, '<span style="color: #0066cc; font-weight: bold;">' + keyword + '</span>');
                });
                
                content = content.replace(/--[^\n]*/g, '<span style="color: #008000; font-style: italic;">$&</span>');
                content = content.replace(/\bsorry\b/g, '<span style="background: #ffcccc; color: #cc0000; font-weight: bold; padding: 1px 3px; border-radius: 2px;">sorry</span>');
                
                codeElement.innerHTML = content;
            });
        });
    </script>
</body>
</html>
"@
}

# Process each selected file
$ProcessedFiles = @()
foreach ($file in $SelectedFiles) {
    Write-Host "📄 Processing: $($file.DisplayName)" -ForegroundColor Cyan
    
    if (!(Test-Path $file.Path)) {
        Write-Host "  ❌ File not found: $($file.Path)" -ForegroundColor Red
        continue
    }
    
    try {
        $FileContent = Get-Content $file.Path -Raw -Encoding UTF8
        if ([string]::IsNullOrWhiteSpace($FileContent)) {
            $FileContent = "-- File appears to be empty or could not be read properly"
        }
    } catch {
        Write-Host "  ❌ Could not read file: $($_.Exception.Message)" -ForegroundColor Red
        continue
    }
    
    # Create individual HTML and PDF
    $HtmlFile = Join-Path $OutputDir "$($file.Name).html"
    $PdfFile = Join-Path $OutputDir "$($file.Name).pdf"
    
    $HtmlContent = Generate-HtmlContent -Title $file.Name -Content $FileContent -Description $file.Description -FilePath $file.Path -FileType $file.Type
    
    try {
        $HtmlContent | Out-File -FilePath $HtmlFile -Encoding UTF8
        Write-Host "  ✅ HTML: $($file.Name).html" -ForegroundColor Green
        
        if (Convert-HtmlToPdf -HtmlPath $HtmlFile -PdfPath $PdfFile) {
            Write-Host "  ✅ PDF: $($file.Name).pdf" -ForegroundColor Green
        } else {
            Write-Host "  ⚠️ PDF creation failed for $($file.Name)" -ForegroundColor Yellow
        }
        
        $ProcessedFiles += @{
            Name = $file.Name
            Content = $FileContent
            Description = $file.Description
            FilePath = $file.Path
            FileType = $file.Type
        }
    } catch {
        Write-Host "  ❌ Could not create files: $($_.Exception.Message)" -ForegroundColor Red
    }
}

# Create combined document
if ($ProcessedFiles.Count -gt 1) {
    Write-Host ""
    Write-Host "📚 Creating combined document: $customTitle" -ForegroundColor Cyan
    
    $CombinedContent = ""
    $TableOfContents = ""
    
    foreach ($file in $ProcessedFiles) {
        $TableOfContents += "- [$($file.Name)]($($file.FilePath))`n"
        $CombinedContent += "`n`n# $($file.Name)`n`n"
        if ($file.Description) {
            $CombinedContent += "**Description:** $($file.Description)`n`n"
        }
        $CombinedContent += "**File:** ``$($file.FilePath)```n`n"
        $CombinedContent += "``````$($file.FileType.ToLower())`n"
        $CombinedContent += $file.Content
        $CombinedContent += "`n``````"
        $CombinedContent += "`n`n---"
    }
    
    $FullCombinedContent = "# $customTitle`n`nCustom selection and ordering of project files.`n`n## Table of Contents`n`n$TableOfContents`n$CombinedContent"
    
    $HtmlFile = Join-Path $OutputDir "$customTitle.html"
    $PdfFile = Join-Path $OutputDir "$customTitle.pdf"
    
    $HtmlContent = Generate-HtmlContent -Title $customTitle -Content $FullCombinedContent -Description "Custom selection and ordering of project files" -FilePath "Combined Document" -FileType "markdown"
    
    try {
        $HtmlContent | Out-File -FilePath $HtmlFile -Encoding UTF8
        Write-Host "  ✅ Combined HTML: $customTitle.html" -ForegroundColor Green
        
        if (Convert-HtmlToPdf -HtmlPath $HtmlFile -PdfPath $PdfFile) {
            Write-Host "  ✅ Combined PDF: $customTitle.pdf" -ForegroundColor Green
        }
    } catch {
        Write-Host "  ❌ Could not create combined files: $($_.Exception.Message)" -ForegroundColor Red
    }
}

Write-Host ""
Write-Host "🎉 AD HOC CONVERSION COMPLETE!" -ForegroundColor Green
Write-Host "📂 Files created in: $OutputDir" -ForegroundColor White

Write-Host ""
Write-Host "📋 Your custom selection:" -ForegroundColor Cyan
foreach ($file in $SelectedFiles) {
    Write-Host "  • $($file.DisplayName)" -ForegroundColor Gray
}