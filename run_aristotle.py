import asyncio
import aristotlelib

async def main():
    # Prove a theorem from a Lean file
    solution_path = await aristotlelib.Project.prove_from_file("/home/kebekus/Mathe/ProjectVD/VD/Aristotle.lean")
    print(f"Solution saved to: {solution_path}")

asyncio.run(main())
