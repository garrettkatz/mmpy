from .setmm import load_pl
from .environment import Environment

if __name__ == "__main__":

    db = load_pl()
    env = Environment(db)
    
    while True:
        label = input("Enter label (q to quit): ")

        if label == "q":
            break

        if label not in db.rules:
            print("No rule called {label}, try again.")
            continue

        new_env = env.copy()
        _, msg = new_env.step(label)

        if msg != "":
            print("Invalid rule: " + msg)
            print("try again.")
            continue

        env = new_env

        print("proof: " + " ".join(env.proof))
        print("stack:")
        for s, step in enumerate(env.stack):
            print(" ", s, step)
        print(f"{len(env.proof)} steps so far...\n")
    
