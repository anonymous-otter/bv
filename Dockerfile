# Use the official Dafny image from Microsoft
FROM mcr.microsoft.com/dotnet/sdk:6.0 AS build

# Install Dafny (latest release)
ENV DAFNY_VERSION=4.6.0
RUN apt-get update && \
    apt-get install -y wget unzip && \
    wget https://github.com/dafny-lang/dafny/releases/download/v${DAFNY_VERSION}/dafny-${DAFNY_VERSION}-x64-ubuntu-20.04.zip && \
    unzip dafny-${DAFNY_VERSION}-x64-ubuntu-20.04.zip -d /opt && \
    rm dafny-${DAFNY_VERSION}-x64-ubuntu-20.04.zip

# Set working directory
WORKDIR /app

# Copy the project into the container
COPY . .

# Default command to verify the Dafny project
CMD ["/opt/dafny/dafny", "verify", "dfyconfig.toml"]