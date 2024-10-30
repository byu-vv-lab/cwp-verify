#!/bin/sh

# Intall JRE for the ANTLRv4 tools
sudo apt update --assume-yes
sudo apt upgrade --assume-yes
sudo apt install default-jre --assume-yes
sudo apt install graphviz --assume-yes

# Upgrade pip
pip install --upgrade pip

# Install the package
pip install --user --editable ".[dev]"

# Install pre-commit
pre-commit install
