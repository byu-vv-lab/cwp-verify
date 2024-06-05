FROM rlespinasse/drawio-desktop-headless

WORKDIR "/opt/bpmn-cwp-verification"

RUN apt update
RUN apt install --yes python3 python3-pip
RUN pip install numpy
RUN pip install pandas

RUN apt --yes install npm
RUN apt install --yes chromium
RUN npm install -g bpmn-to-image
RUN apt install --yes graphicsmagick-imagemagick-compat
RUN apt install spin

# replace shell with bash so we can source files
RUN rm /bin/sh && ln -s /bin/bash /bin/sh

# update the repository sources list
# and install dependencies
RUN apt-get update \
    && apt-get install -y curl \
    && apt-get -y autoclean

# nvm environment variables
ENV NVM_DIR /usr/local/nvm
ENV NODE_VERSION 16

# install nvm
# https://github.com/creationix/nvm#install-script
RUN curl --silent -o- https://raw.githubusercontent.com/creationix/nvm/v0.31.2/install.sh | bash

# install node and npm
RUN source $NVM_DIR/nvm.sh \
    && nvm install $NODE_VERSION \
    && nvm alias default $NODE_VERSION \
    && nvm use default

# add node and npm to path so the commands are available
ENV NODE_PATH $NVM_DIR/v$NODE_VERSION/lib/node_modules
ENV PATH $NVM_DIR/versions/node/v$NODE_VERSION/bin:$PATH

RUN mkdir code

COPY test code/test
COPY src code/src
COPY src/Util/chromium-browser /usr/bin/
COPY launch_verify.sh code

ENTRYPOINT [ "/opt/bpmn-cwp-verification/code/launch_verify.sh" ]
CMD [ "--help" ]
