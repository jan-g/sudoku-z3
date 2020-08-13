from setuptools import setup, find_packages


setup(
    name="sudoku",
    versioning="dev",
    setup_requires=["setupmeta"],
    packages=find_packages(exclude=["test.*, *.test", "test*"]),
)
