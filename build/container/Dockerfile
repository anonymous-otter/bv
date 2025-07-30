FROM ubuntu:22.04

# Installing required packages.
# Source: https://source.android.com/docs/setup/start/requirements
RUN apt-get update && apt-get install -y \
    git-core gnupg flex bison build-essential zip curl zlib1g-dev \
    libc6-dev-i386 libncurses5 lib32ncurses5-dev x11proto-core-dev \
    libx11-dev lib32z1-dev libgl1-mesa-dev libxml2-utils xsltproc unzip \
    fontconfig \
    udev \
    ;

# Installing additional required packages.
RUN apt-get update && apt-get install -y \
    sudo \
    dotnet-sdk-8.0 \
    wget rsync \
    libffi-dev libssl-dev \
    python3.9 \
    ;

# Installing repo manually to have the latest version.
# Source: https://source.android.com/docs/setup/start/requirements#repo
RUN export REPO=$(mktemp /tmp/repo.XXXXXXXXX) && \
    curl -o ${REPO} https://storage.googleapis.com/git-repo-downloads/repo && \
    gpg --recv-key 8BB9AD793E8E6153AF0F9A4416530D5E920F5C65 && \
    curl -s https://storage.googleapis.com/git-repo-downloads/repo.asc \
    | gpg --verify - ${REPO} && install -m 755 ${REPO} /usr/local/bin/repo

# Installing Dafny
ARG DAFNY_BIN_URL=https://github.com/dafny-lang/dafny/releases/download/v4.9.1/dafny-4.9.1-x64-ubuntu-20.04.zip
ARG DAFNY_VERSION=4.9.1
ENV DAFNY_INSTALL_PATH=/usr/local/bin/dafny-${DAFNY_VERSION}
ENV DAFNY_HOME=${DAFNY_INSTALL_PATH}/dafny
RUN DAFNY_ZIP=mktemp && \
    wget ${DAFNY_BIN_URL} -O ${DAFNY_ZIP} && \
    unzip ${DAFNY_ZIP} -d ${DAFNY_INSTALL_PATH} && \
    ln -s ${DAFNY_HOME}/dafny /usr/local/bin/dafny

# Installing Android SDK Platform-Tools
ARG PLATFORM_TOOLS_URL=https://dl.google.com/android/repository/platform-tools_r34.0.4-linux.zip
ENV ANDROID_SDK_PATH=/usr/local/bin/android_sdk
ENV PLATFORM_TOOLS_INSTALL_PATH=${ANDROID_SDK_PATH}/platform-tools
RUN PLATFORM_TOOLS_ZIP=mktemp && \
    wget ${PLATFORM_TOOLS_URL} -O ${PLATFORM_TOOLS_ZIP} && \
    unzip ${PLATFORM_TOOLS_ZIP} -d ${ANDROID_SDK_PATH} && \
    PLATFORM_TOOLS_PATH=${ANDROID_SDK_PATH}/platform-tools && \
    ln -s ${PLATFORM_TOOLS_PATH}/adb /usr/local/bin/adb

COPY scripts /root/scripts