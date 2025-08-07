param(
    [string[]]$Files,
    [string]$OutputDir = "C:\Users\Moses\math_ops\OperatorKernelO6\Docs",
    [string]$Title = "Custom_Selection"
)

Write-Host "JUPYTER FILE CONVERTER" -ForegroundColor Cyan
Write-Host "Beautiful academic-style HTML & PDF conversion" -ForegroundColor Green
Write-Host ""

if (!$Files -or $Files.Count -eq 0) {
    Write-Host "No files provided!" -ForegroundColor Red
    Write-Host "Usage: .\jupyter_converter.ps1 -Files @('file1.md', 'file2.lean') -Title 'MyDoc'" -ForegroundColor Yellow
    exit
}

# Validate files
$validFiles = @()
Write-Host "Validating files:" -ForegroundColor White
foreach ($file in $Files) {
    $fileName = [System.IO.Path]::GetFileName($file)
    if (Test-Path $file) {
        Write-Host "  ✓ $fileName" -ForegroundColor Green
        $validFiles += $file
    } else {
        Write-Host "  ✗ $fileName (not found)" -ForegroundColor Red
    }
}

if ($validFiles.Count -eq 0) {
    Write-Host "No valid files found!" -ForegroundColor Red
    exit
}

# Create output directory
New-Item -ItemType Directory -Path $OutputDir -Force | Out-Null
Add-Type -AssemblyName System.Web

Write-Host ""
Write-Host "Processing $($validFiles.Count) files..." -ForegroundColor White

$processed = @()
$index = 1

foreach ($file in $validFiles) {
    $name = [System.IO.Path]::GetFileNameWithoutExtension($file)
    $isMarkdown = $file -like "*.md"
    
    Write-Host "[$index/$($validFiles.Count)] $name" -ForegroundColor White
    
    # Read content
    $content = Get-Content $file -Raw -Encoding UTF8
    if (!$content) { $content = "-- File appears to be empty --" }
    
    # Create HTML with academic styling
    $htmlContent = if ($isMarkdown) {
        # Enhanced markdown to HTML conversion
        $html = $content
        $html = $html -replace '(?m)^### (.*)', '<h3>$1</h3>'
        $html = $html -replace '(?m)^## (.*)', '<h2>$1</h2>'
        $html = $html -replace '(?m)^# (.*)', '<h1 class="doc-header">$1</h1>'
        $html = $html -replace '\*\*([^*]+)\*\*', '<strong>$1</strong>'
        $html = $html -replace '\*([^*]+)\*', '<em>$1</em>'
        $html = $html -replace '`([^`]+)`', '<code>$1</code>'
        # Convert line breaks to paragraphs
        $html = $html -replace '(?m)^\s*$', '</p><p>'
        $html = $html -replace '^', '<p>'
        $html = $html -replace '$', '</p>'
        $html = $html -replace '<p></p>', ''
        "<div class='markdown'>$html</div>"
    } else {
        "<pre class='lean-code'>" + [System.Web.HttpUtility]::HtmlEncode($content) + "</pre>"
    }
    
    # Academic journal style HTML template
    $htmlTemplate = @'
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{0}</title>
    <style>
        body {{ 
            max-width: 800px; 
            margin: 0 auto; 
            padding: 40px 30px; 
            font-family: 'Times New Roman', Times, serif;
            font-size: 12pt;
            line-height: 1.6;
            color: #000;
            background: #fff;
        }}
        
        .header {{
            text-align: center;
            margin-bottom: 40px;
            border-bottom: 2px solid #000;
            padding-bottom: 20px;
        }}
        
        .title {{
            font-size: 18pt;
            font-weight: bold;
            margin-bottom: 10px;
            text-transform: uppercase;
            letter-spacing: 1px;
        }}
        
        .author {{
            font-size: 14pt;
            font-style: italic;
            margin-bottom: 5px;
        }}
        
        .affiliation {{
            font-size: 11pt;
            color: #666;
        }}
        
        h1, .doc-header {{ 
            font-size: 16pt;
            font-weight: bold;
            color: #000;
            margin-top: 30px;
            margin-bottom: 15px;
            text-align: center;
            text-transform: uppercase;
            letter-spacing: 0.5px;
        }}
        
        h2 {{ 
            font-size: 14pt;
            font-weight: bold;
            color: #000;
            margin-top: 25px;
            margin-bottom: 12px;
            border-bottom: 1px solid #ccc;
            padding-bottom: 5px;
        }}
        
        h3 {{ 
            font-size: 12pt;
            font-weight: bold;
            color: #000;
            margin-top: 20px;
            margin-bottom: 10px;
        }}
        
        p {{
            text-align: justify;
            margin-bottom: 12pt;
            text-indent: 0.5in;
        }}
        
        .lean-code {{ 
            background: #f9f9f9; 
            padding: 15pt; 
            border: 1px solid #ddd;
            font-family: 'Courier New', Courier, monospace;
            font-size: 10pt;
            line-height: 1.4;
            overflow-x: auto;
            white-space: pre-wrap;
            margin: 15pt 0;
        }}
        
        .markdown {{ 
            text-align: justify;
        }}
        
        code {{ 
            background: #f5f5f5;
            padding: 2pt 4pt;
            border: 1px solid #ddd;
            font-family: 'Courier New', monospace;
            font-size: 10pt;
        }}
        
        strong {{
            font-weight: bold;
        }}
        
        em {{
            font-style: italic;
        }}
        
        .file-info {{
            background: #f0f0f0;
            border: 1px solid #ccc;
            padding: 10pt;
            margin: 20pt 0;
            font-size: 10pt;
            color: #666;
        }}
        
        .no-print {{ display: block; }}
    </style>
</head>
<body>
    <div class="header">
        <div class="title">{1}</div>
        <div class="author">Moses Rahnama</div>
        <div class="affiliation">Mina Analytics</div>
    </div>
    
    <div class="file-info no-print">
        <strong>Source File:</strong> {2}<br>
        <strong>Document Type:</strong> {3}<br>
        <strong>Generated:</strong> {4}
    </div>
    
    {5}
</body>
</html>
'@

    $docType = if ($isMarkdown) { 'Markdown Document' } else { 'Lean Proof Code' }
    $timestamp = Get-Date -Format 'MMMM d, yyyy \a\t h:mm tt'
    $html = $htmlTemplate -f $name, $name, $file, $docType, $timestamp, $htmlContent
    
    # Save individual HTML file
    $safeName = $name -replace '[^\w\-]', '_'
    $outputPath = Join-Path $OutputDir "$safeName.html"
    $html | Out-File -FilePath $outputPath -Encoding UTF8
    Write-Host "    ✓ $safeName.html" -ForegroundColor Green
    
    # Generate PDF using wkhtmltopdf if available
    try {
        $pdfPath = Join-Path $OutputDir "$safeName.pdf"
        & wkhtmltopdf --page-size A4 --margin-top 1in --margin-bottom 1in --margin-left 1in --margin-right 1in "$outputPath" "$pdfPath" 2>$null
        if ($LASTEXITCODE -eq 0) {
            Write-Host "    ✓ $safeName.pdf" -ForegroundColor Green
        }
    } catch {
        # wkhtmltopdf not available - skip PDF generation
    }
    
    $processed += @{
        Name = $name
        Content = $content
        Type = if ($isMarkdown) { "markdown" } else { "lean" }
        Path = $file
    }
    
    $index++
}

# Create combined document
if ($processed.Count -gt 1) {
    Write-Host ""
    Write-Host "Creating combined document..." -ForegroundColor Cyan
    
    # Build combined HTML with academic styling using proper string formatting
    $combinedHtmlTemplate = @'
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <title>{0} Combined</title>
    <style>
        body {{ 
            max-width: 800px; 
            margin: 0 auto; 
            padding: 40px 30px; 
            font-family: 'Times New Roman', Times, serif;
            font-size: 12pt;
            line-height: 1.6;
            color: #000;
            background: #fff;
        }}
        
        .header {{
            text-align: center;
            margin-bottom: 40px;
            border-bottom: 2px solid #000;
            padding-bottom: 20px;
        }}
        
        .title {{
            font-size: 20pt;
            font-weight: bold;
            margin-bottom: 10px;
            text-transform: uppercase;
            letter-spacing: 1px;
        }}
        
        .author {{
            font-size: 14pt;
            font-style: italic;
            margin-bottom: 5px;
        }}
        
        .affiliation {{
            font-size: 11pt;
            color: #666;
        }}
        
        .toc {{
            background: #f9f9f9;
            border: 1px solid #ddd;
            padding: 20pt;
            margin: 30pt 0;
        }}
        
        .toc h2 {{
            margin-top: 0;
            font-size: 14pt;
            text-align: center;
        }}
        
        .toc ul {{
            list-style-type: decimal;
            padding-left: 30pt;
        }}
        
        .toc li {{
            margin-bottom: 8pt;
        }}
        
        h1 {{ 
            font-size: 16pt;
            font-weight: bold;
            color: #000;
            margin-top: 40pt;
            margin-bottom: 15pt;
            text-align: center;
            text-transform: uppercase;
            letter-spacing: 0.5px;
        }}
        
        h2 {{ 
            font-size: 14pt;
            font-weight: bold;
            color: #000;
            margin-top: 25pt;
            margin-bottom: 12pt;
            border-bottom: 1px solid #ccc;
            padding-bottom: 5pt;
        }}
        
        .file-section {{
            margin-bottom: 40pt;
            border-bottom: 1px solid #eee;
            padding-bottom: 20pt;
        }}
        
        .source-info {{
            background: #f5f5f5;
            padding: 10pt;
            margin: 15pt 0;
            font-size: 10pt;
            color: #666;
            border-left: 4px solid #ccc;
        }}
        
        pre {{ 
            background: #f9f9f9; 
            padding: 15pt; 
            border: 1px solid #ddd;
            font-family: 'Courier New', Courier, monospace;
            font-size: 10pt;
            line-height: 1.4;
            overflow-x: auto;
            white-space: pre-wrap;
            margin: 15pt 0;
        }}
    </style>
</head>
<body>
    <div class="header">
        <div class="title">{1}</div>
        <div class="author">Moses Rahnama</div>
        <div class="affiliation">Mina Analytics</div>
    </div>
    
    <div class="toc">
        <h2>Table of Contents</h2>
        <ul>
{2}        </ul>
    </div>
{3}</body>
</html>
'@

    # Build table of contents
    $tocItems = ""
    foreach ($file in $processed) {
        $tocItems += '            <li>' + $file.Name + '</li>' + "`n"
    }
    
    # Build file sections
    $fileSections = ""
    foreach ($file in $processed) {
        $fileSections += '    <div class="file-section">' + "`n"
        $fileSections += '        <h1>' + $file.Name + '</h1>' + "`n"
        $fileSections += '        <div class="source-info">' + "`n"
        $fileSections += '            <strong>Source:</strong> ' + $file.Path + '<br>' + "`n"
        $fileSections += '            <strong>Type:</strong> ' + $file.Type.ToUpper() + "`n"
        $fileSections += '        </div>' + "`n"
        $fileSections += '        <pre>' + [System.Web.HttpUtility]::HtmlEncode($file.Content) + '</pre>' + "`n"
        $fileSections += '    </div>' + "`n`n"
    }
    
    $combinedContent = $combinedHtmlTemplate -f $Title, $Title, $tocItems, $fileSections
    
    $combinedPath = Join-Path $OutputDir "$Title`_Combined.html"
    $combinedContent | Out-File -FilePath $combinedPath -Encoding UTF8
    Write-Host "    ✓ $Title`_Combined.html" -ForegroundColor Green
    
    # Generate combined PDF
    try {
        $combinedPdfPath = Join-Path $OutputDir "$Title`_Combined.pdf"
        & wkhtmltopdf --page-size A4 --margin-top 1in --margin-bottom 1in --margin-left 1in --margin-right 1in "$combinedPath" "$combinedPdfPath" 2>$null
        if ($LASTEXITCODE -eq 0) {
            Write-Host "    ✓ $Title`_Combined.pdf" -ForegroundColor Green
        }
    } catch {
        # wkhtmltopdf not available - skip PDF generation
    }
}

Write-Host ""
Write-Host "CONVERSION COMPLETE!" -ForegroundColor Green
Write-Host "Output directory: $OutputDir" -ForegroundColor White
Write-Host "Files processed: $($processed.Count)" -ForegroundColor Gray
if ($processed.Count -gt 1) {
    Write-Host "Combined document: Yes (HTML + PDF if wkhtmltopdf available)" -ForegroundColor Gray
}

Write-Host ""
Write-Host "🎓 Academic journal styling applied" -ForegroundColor Yellow
Write-Host "📄 Both HTML and PDF formats generated" -ForegroundColor Yellow
Write-Host "✨ Ready for publication!" -ForegroundColor Yellow