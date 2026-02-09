"""
pip install blessed
"""

from blessed import Terminal
from blessed.keyboard import Keystroke
import metamathpy.setmm as ms

if __name__ == "__main__":

    term = Terminal()
    db = ms.load_pl()

    rule_labels = [label
        for label in db.rules.keys()
            if db.rules[label].consequent.tag in ("$p", "$a")]
    rule_index = 0

    # mm_code = db.rules[rule_labels[rule_index]].mm()
    # mm_code.replace("\n", "\n" + term.clear_eol)
    # print(mm_code)
    # input('.')

    # should check and branch on mouse support
    # https://blessed.readthedocs.io/en/latest/api/terminal.html#blessed.terminal.Terminal.does_mouse

    with term.fullscreen(), term.no_line_wrap(), term.mouse_enabled(), term.cbreak(), term.hidden_cursor():
    
        while True:

            H, W = term.height, term.width

            # eventually don't print everywhere, only the changes
            mm_lines = []
            rule_offset = 0
            while len(mm_lines) < H:
                mm_rule = db.rules[rule_labels[rule_index + rule_offset]].mm()
                mm_lines = mm_lines + mm_rule.split("\n")
                rule_offset += 1
            mm_lines = mm_lines[:H]
            # mm_code.replace("\n", term.clear_eol + "\n")

            # make cursor in center, not top
            mm_lines[0] = term.black_on_white(mm_lines[0] + term.clear_eol)
            mm_lines[1:] = [line + term.clear_eol for line in mm_lines[1:]]

            # print(term.move_xy(0,0) + mm_code + term.clear_eol, end='', flush=True)
            # print((term.clear_eol+"\n")*4, end='', flush=True)

            for offset in range(H):
                if offset < len(mm_lines):
                    # print(term.move_xy(0,offset) + mm_lines[offset] + term.clear_eol, end='', flush=True)
                    print(term.move_xy(0,offset) + mm_lines[offset], end='', flush=True)
                else:
                    print(term.move_xy(0,offset) + term.clear_eol, end='', flush=True)

            # https://blessed.readthedocs.io/en/latest/measuring.html#
            print(term.move_xy(0,H-1) + f"[{rule_index} of {len(db.rules)}, {H//2} of {H}, 0 of {W}]" + term.clear_eol, end='', flush=True)

            # # the clear_eol (end of line) could be useful when backtracking the iterative deepening proof search.
            # print(term.move_xy(10, 5) + f"here" + term.move_xy(12,3) + "also here" + term.clear_eol, end='', flush=True)

            # all key names:
            # https://blessed.readthedocs.io/en/latest/keyboard.html#all-names

            inp = term.inkey(timeout=0.1)

            if inp.is_sequence:
                # print(f"Special key: {inp.name} ({inp!r})")

                if inp.is_up(): rule_index = max(rule_index - 1, 0)
                if inp.is_down(): rule_index = (rule_index + 1) % len(db.rules)

            elif hasattr(inp, "name") and inp.name is not None and inp.name.startswith("MOUSE_"):
                print(repr(inp.name))
                print(inp.mouse_yx)

            elif inp == "q":
                break

        
