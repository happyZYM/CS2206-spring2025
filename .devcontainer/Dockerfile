FROM qcp:0424-coq8.15.2

# Switch to root for package installation
USER root

# Install GPG and related tools
RUN apt-get update && \
    apt-get install -y \
    git \
    && rm -rf /var/lib/apt/lists/*
