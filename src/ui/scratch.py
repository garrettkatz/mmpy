"""
pip install blessed
"""
from blessed import Terminal

term = Terminal()

with term.fullscreen(), term.no_line_wrap():
    print(term.home + term.clear + term.move_y(term.height // 2))
    print(term.black_on_darkkhaki(term.center('press any key to continue.')))
    
    with term.cbreak(), term.hidden_cursor():
        inp = term.inkey()
    
    print(term.move_down(2) + 'You pressed ' + term.bold(repr(inp)))

    input("Enter to end...")
    
