# Keeping the prompt under the context-length ceiling

## 1 · Put the growing proof in a file
• Maintain the evolving proof in this repository instead of the chat (e.g. in `proofs/target_theorem.md`).  
• Use `edit_existing_file` so only diffs are echoed, keeping prompts short.  
• The full proof never counts against the token budget—only incremental changes do.

## 2 · Summarize chat history regularly
• After a few exchanges, condense the discussion (questions, clarifications, decisions) into a short bullet list.  
• Old verbose turns can then be pruned by the frontend or simply not re-pasted.

## 3 · Avoid repeating tool schemas & instructions
• The tool list and “always include language + file” rule live in system/developer messages; do **not** quote them again inside prompts.

## 4 · Keep bulky artefacts out of inline chat
• For large lemmas, code, or logs, store them in repo files or paste-links and refer to the path/URL instead of pasting the whole text.

## 5 · Split mega-tasks into sub-threads
• If a task spans many pages, handle subsections in separate turns, summarise, then fold the summary into the main thread.

## 6 · Leave ~1 000 tokens head-room
• Keep each prompt comfortably under ~3 000 tokens.  
• The assistant will keep answers concise unless full detail is explicitly requested.

---

### Concrete next step
Create/maintain `proofs/target_theorem.md` with the latest proof state. Future edits will be tiny diffs, ensuring we stay well below the context limit.
