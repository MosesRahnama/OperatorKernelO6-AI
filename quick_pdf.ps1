# Combine all Lean files into one
$Output = "c:\Users\Moses\math_ops\OperatorKernelO6\Combined_Code.txt"

"OperatorKernelO6 - Complete Lean 4 Code`n" + "="*50 + "`n" | Out-File $Output

Get-ChildItem -Path "c:\Users\Moses\math_ops\OperatorKernelO6\OperatorKernelO6" -Filter "*.lean" -Recurse | ForEach-Object {
    "`n" + $_.Name + "`n" + "-"*30 + "`n" | Out-File $Output -Append
    Get-Content $_.FullName | Out-File $Output -Append
}

Write-Host "Combined file created: $Output"
Write-Host "Open in Notepad++, apply Lean syntax highlighting, then print to PDF!"
