# Earlier Version

This is the first version of the workshop. It parsed a small Lean-like
language with its own parser and checked it with a simplified kernel, one
`solution.py` per chapter. It was replaced by the version in the repository
root, which checks the trees real Lean produces.

It is kept for reference and is not maintained. To run it, from this folder:

```bash
python3 -m pip install -r requirements.txt
```

```bash
python3 -B -m pylean.tutorial_type_checker all
```
