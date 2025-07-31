#!/usr/bin/env python3
"""Lean‑4 Debugger → o3‑pro (async, max tokens, store enabled)
------------------------------------------------------------
Updated GUI with:
• Background mode (async) with valid 'store': True
• max_output_tokens = 100000 to avoid 'incomplete'
• reasoning: {effort: high} for deeper RL reasoning
• robust timeouts and error handling
------------------------------------------------------------

import tkinter as tk
from tkinter import filedialog, scrolledtext, messagebox
import threading, time, requests, json
from pathlib import Path

# 🔐 API KEY
api_key = "sk-xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"

# Context files (update paths as needed)
EXTRA_FILES = [
    r"C:\Users\Moses\math_ops\OperatorMath\Basic.lean",
    r"C:\Users\Moses\math_ops\OperatorMath\Negation.lean",
    r"C:\Users\Moses\math_ops\OperatorMath\NumericFixedPoint.lean",
]

def read_context_files():
    parts = []
    for fp in EXTRA_FILES:
        p = Path(fp)
        if p.exists():
            parts.append(f"\n-- >>> {p.name} <<<\n{p.read_text(encoding='utf-8')}")
    return "\n".join(parts)

def build_prompt(code: str, errors: str) -> str:
    ctx = read_context_files()
    errblock = f"=== Errors ===\n{errors}\n" if errors.strip() else ""
    return f"""You are a Lean 4 expert. Below are trusted context files that already compile:

=== Context modules ===
{ctx}

{errblock}=== User snippet ===
{code}

TASKS
1. Type‑check/compile this snippet in Lean.
2. Diagnose each error with a brief comment (`-- error:`).
3. Provide ONE corrected Lean snippet that compiles without mathlib/Std.
4. Use only operator‑based fixed‑point machinery—no axioms, `sorry`, or numeric methods.
Output only the corrected Lean code, wrapped in a single ```lean``` fence.
"""

def call_o3pro_async(code: str, errors: str, cb):
    url = "https://api.openai.com/v1/responses"
    headers = {"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"}
    payload = {
        "model": "o3-pro",
        "input": build_prompt(code, errors),
        "background": True,
        "max_output_tokens": 100000,
        "store": True,
        "reasoning": {"effort": "high"}
    }
    try:
        cb("⏳ Job submitted, awaiting ID…\n")
        r = requests.post(url, headers=headers, json=payload, timeout=300)
        r.raise_for_status()
        data = r.json()
        job_id = data.get("id")
        if not job_id:
            cb("❌ ERROR: No job ID returned\n")
            return
        cb(f"✅ Job ID: {job_id}\n")
        poll_url = f"{url}/{job_id}"
        last_status = None
        while True:
            time.sleep(10)
            p = requests.get(poll_url, headers=headers, timeout=300)
            p.raise_for_status()
            data = p.json()
            status = data.get("status", "")
            if status in ("queued", "running", "pending"):
                if status != last_status:
                    cb(f"⏳ Status: {status}\n")
                    last_status = status
                continue
            if status == "failed":
                cb(f"❌ Job failed: {data.get('error', 'no details')}\n")
                return
            if status == "completed":
                txt = ""
                for part in data.get("results", []) + data.get("choices", []):
                    if part.get("type") in ("output_text", "message"):
                        txt = part.get("text") or part.get("content", "")
                        if txt: break
                if not txt:
                    txt = json.dumps(data, indent=2)
                cb("🎉 Completed\n\n" + txt + "\n")
                return
    except requests.exceptions.Timeout:
        cb("❌ ERROR: Request timed out. The operation took too long.\n")
    except requests.exceptions.HTTPError as e:
        resp = e.response
        err_msg = ""
        if resp is not None:
            try:
                err_json = resp.json()
                err_msg = err_json.get('error', {}).get('message', '') or resp.text
            except ValueError:
                err_msg = resp.text or str(e)
            cb(f"❌ HTTP {resp.status_code} Error: {err_msg.strip()}\n")
        else:
            cb(f"❌ HTTP Error: {e}\n")
    except Exception as e:
        cb(f"❌ ERROR: {e}\n")

class LeanO3GUI:
    def __init__(self, root: tk.Tk):
        self.root = root
        root.title("Lean 4 Debugger → o3‑pro (async, max, store)")
        self.editor = scrolledtext.ScrolledText(root, wrap=tk.NONE, height=18)
        self.editor.pack(fill=tk.BOTH, expand=True, padx=4, pady=2)
        tk.Label(root, text="Paste Lean error messages (optional):").pack()
        self.errbox = scrolledtext.ScrolledText(root, wrap=tk.NONE, height=6, bg="#222", fg="#ff9191")
        self.errbox.pack(fill=tk.BOTH, padx=4, pady=2)
        frame = tk.Frame(root); frame.pack(pady=3)
        tk.Button(frame, text="📂 Load *.lean", command=self.load_file).pack(side=tk.LEFT, padx=3)
        self.send_btn = tk.Button(frame, text="🚀 Send to o3‑pro", command=self.send)
        self.send_btn.pack(side=tk.LEFT, padx=3)
        self.retry_btn = tk.Button(frame, text="🔁 Retry", command=self.retry, state=tk.DISABLED)
        self.retry_btn.pack(side=tk.LEFT, padx=3)
        self.out = scrolledtext.ScrolledText(root, wrap=tk.NONE, height=16, bg="#111", fg="#eee")
        self.out.pack(fill=tk.BOTH, expand=True, padx=4, pady=2)
        self.last = ("", "")

    def append(self, msg):
        self.out.insert(tk.END, msg); self.out.see(tk.END)
    def cb(self, msg):
        def ui_update():
            self.append(msg)
            if msg.startswith(("🎉","❌")):
                self.enable()
        self.root.after(0, ui_update)

    def enable(self):
        self.send_btn.config(state="normal")
        self.retry_btn.config(state="normal")

    def load_file(self):
        fp = filedialog.askopenfilename(filetypes=[("Lean files","*.lean")])
        if not fp: return
        self.editor.delete("1.0", tk.END)
        self.editor.insert(tk.END, Path(fp).read_text(encoding='utf-8'))
        self.out.delete("1.0", tk.END)

    def send(self):
        code = self.editor.get("1.0", tk.END).rstrip()
        if not code:
            messagebox.showwarning("No code","Load or paste Lean code first")
            return
        errors = self.errbox.get("1.0", tk.END).rstrip()
        self.last = (code, errors)
        self.out.delete("1.0", tk.END)
        self.send_btn.config(state="disabled")
        self.retry_btn.config(state="disabled")
        threading.Thread(target=call_o3pro_async, args=(code, errors, self.cb), daemon=True).start()

    def retry(self):
        code, errors = self.last
        if not code:
            return
        self.out.delete("1.0", tk.END)
        self.send_btn.config(state="disabled")
        self.retry_btn.config(state="disabled")
        threading.Thread(target=call_o3pro_async, args=(code, errors, self.cb), daemon=True).start()

if __name__ == "__main__":
    root = tk.Tk()
    LeanO3GUI(root)
    root.mainloop()
