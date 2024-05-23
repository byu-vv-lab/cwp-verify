## Developer Setup

The following assume the terminal is in the root directory of the package.

  1. Create a virtual environment
      * In the root directory: `python3 -m venv .venv`
      * Activate the virtual environment: `source .venv/bin/activate`
  2. Install `setuptools`
      * `pip install --upgrade setuptools`
      * `pip install --upgrade build`
  4. Install the package, with `dev` dependencies, in editable mode: `pip install --editable ".[dev]"`.
  5. Enable `pre-commit`: `pre-commit install`
      * `pre-commit run --all-files` will force the check on all files otherwise it will only check the files in the index (i.e., those that are part if the commit)

  To uninstall the package, `pip uninstall bpmn_cwp_verify`. To deactivate the virtual environment: `deactivate`.
  The package uses `setuptools` and is configured in `pyproject.toml`. If a now dependency is required (added), then please update the `pyproject.toml` file accordingly so that the install brings it down as expected. All of the `pre-commit` hooks are defined in the `.pre-commit-config.yaml`. Please update as needed. It currently uses `ruff` for linting and formatting. It uses `mypy` for static typechecking.

  If using the `mypy` vscode extension, then it is necessary to point the executable path to `.venv/bin/dmypy` for it to work correctly.


## TODO

### Repository organization and entry points

  * Remove the hard coded paths on lines 29 and 30 of `cli/main.py` to take the relative path specified in the command line. Add runtime checks, with appropriate error messages, that all the required files (BPMN, CWP, state, etc.) are present in the supplied directory.
  * Move the `CSVIngest`, `BMPN-Generate`, and `CWP-Generate` into the test directory
  * Bring over the tests that make sense and add tests as we refactor code.
  * Add an argument to indicate the output directory. Fail if the directory doesn't exist or it doesn't allow read and write permissions
  * Refactor the `src` directory to use appropriate Python package/module names (all lower-case, short, hypens, underscores are allowed)
  * Move code around so that everything to do with CWP is in cwp and everything to do with BPMN is in BPMN etc.
  * Break the `BMPN.py` into several files for flows, nodes, process, and model.

### Input Validation for BPMN

Add list of _best practices for BPMN_ as separate TODO items.

  * Every element has a _unique friendly name_ so that all errors are reported using the friendly name
  * Add a proper expression parser from ANTLRv4 for the FEEL language and make sure all expressions parse

### Input Validation for CWP

  * Add a proper expression parser from ANTLRv4 for the FEEL language and make sure all expressions parse

### Input Validation for state

### Input Validation for Promela for activities (need to look at this more)

### New functionality

  * Add event gates to the BPMN model and Promela generation

# Old README below

Everything below may or may not be relevant going forward.

## Docker

### Usage
  0. Move to the code directory that contains the file `Dockerfile`
  1. Build the image: `docker build --tag cwp-bpmn .`

To run on an example:

  0. Move to the `code` directory that contains the `Dockerfile`, `launch_verify.sh`, and `verify.sh`
  1. Run `verify.sh`: `./verify.sh <directory with example> <directory for output>`

Here is an example (remember to be in the `code` directory):

`./verify.sh assets/examples/face2face_Sep_16_2023_error output/examples`

### Notes

  * `Dockerfile`: commands to build the image needed for `docker run`
  * `code/verify.sh`: this script wraps the `docker run` command. It takes two arguments: the first to indicate the directory holding the example; and the second to indicate where to put the output from the verification. The command will create a directory in the output directory for the output. The script adds the `-e <example name>` needed for the `main.py` to run correctly. There is currently no support for any other command line arguments for `code/src/main.py`.
  * `launch_verify.sh`: this script is the entry point for the docker image. It moves to the `code/src` directory and calls `python3 main.py`. It passes along any arguments from `code/verify.sh` to `code/src/main.py`. There is only one argument currently and that is `-e <example name>`.
  * `code/src/Util/chromium-browser`: this stript is needed in order to launch `/usr/bin/chromium` as `root` with **no sandbox**. A headless instance of Chromium is needed for `puppeteer` to work. `puppeteer` is required for `bpmn-to-image` to generate the images of the BPMN in the counter-example generation.
  * `code/src/Util/verify.sh`: this script has been modified to now use the `/opt/bpmn-cwp-verification` directory for the `projectDir`
  * `code/src/main.py`: the main entry point has been modified to no longer use the `drawio` via `docker run` but rather call the entry point directly as `/opt/drawio-desktop/entrypoint.sh`. The original `rlespinasse/drawio-desktop-headless` is included in the `code/Dockerfile` as the starting point for the image here (e.g., it's the **FROM** in `code/Dockerfile`)


## Desktop ##

The below list may be incomplete. See `code/Dockerfile` for the up-to-date required dependencies for a `Linux` installation. Note that the verification part has been tested on Mac OSX. The `spin` install needs to be different though. The counter example generation has only been tested on Linux and Docker. It has not been attempted on Mac OSX.

for verification:

```
pip install numpy
pip install pandas
change projectDir in verify.sh
install spin (sudo apt install spin)
```

For counterexample generation:

``````
sudo apt install graphicsmagick-imagemagick-compat
sudo apt install npm
sudo npm install -g bpmn-to-image
install nvm (curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.39.3/install.sh | bash)
nvm install 16
nvm use 16
```

docker run -it -e DRAWIO_DESKTOP_COMMAND_TIMEOUT='10000s' -w /data -v .:/data rlespinasse/drawio-desktop-headless -x -f png ./"
