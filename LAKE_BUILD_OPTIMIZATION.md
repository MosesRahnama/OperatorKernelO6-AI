# Lake Build Optimization Guide

## 🚨 **Problem**: Lake keeps rebuilding 3000+ mathlib files

This happens because:
1. Cache invalidation when `.lake` folder is deleted
2. Broken import files trigger full rebuilds 
3. No pre-built cache available for your mathlib version

## ✅ **Solution**: Quick Build Script

Save this as `quick-build.ps1`:

```powershell
# Kill any running Lean processes
taskkill /F /IM lean.exe 2>$null

# Remove lock files (but preserve cache)
Remove-Item .lake\*.olean* -Force -ErrorAction SilentlyContinue
Remove-Item .lake\*.lock -Force -ErrorAction SilentlyContinue

# Try to get cached builds
lake exe cache get 2>$null

# Build only project files (not all mathlib)
Write-Host "Building project files only..."
lake -R build OperatorKernelO6.Kernel
lake -R build OperatorKernelO6.Meta.Meta  
lake -R build OperatorKernelO6.Meta.Termination

Write-Host "✅ Quick build complete!"
```

## 🛡️ **Prevention**:

1. **Never run `lake clean`** unless absolutely necessary
2. **Use `lake exe cache get`** before building
3. **Build specific targets**: `lake build YourModule` not `lake build`
4. **Add .gitignore** for build artifacts:
   ```
   .lake/build/
   .lake/lakefile.olean*
   .lake/packages/*/build/
   ```

## 🔧 **If stuck in rebuild hell**:
```bash
# Emergency reset
rm -rf .lake/build  # Keep packages, remove build cache only
lake exe cache get  # Download pre-built if available
lake -R build YourSpecificFile.lean  # Build only what you need
```
