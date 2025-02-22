FROM docker.io/coqorg/coq:8.15-native-flambda

# Switch to root for package installation
USER root

# Install GPG and related tools
RUN apt-get update && \
    apt-get install -y \
    wget \
    gnupg2 \
    && rm -rf /var/lib/apt/lists/*

# Switch back to coq user
USER coq
