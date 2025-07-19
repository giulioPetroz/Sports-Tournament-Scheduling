FROM minizinc/minizinc:latest

WORKDIR /cdmo

# Install dependencies
RUN apt-get update && \
    DEBIAN_FRONTEND=noninteractive apt-get install -y \
    curl bzip2 git unzip && \
    apt-get clean && rm -rf /var/lib/apt/lists/*

# Install Miniconda
ENV CONDA_DIR=/opt/conda
RUN curl -LO "https://repo.anaconda.com/miniconda/Miniconda3-latest-Linux-x86_64.sh" && \
    bash Miniconda3-latest-Linux-x86_64.sh -b -p $CONDA_DIR && \
    rm Miniconda3-latest-Linux-x86_64.sh && \
    $CONDA_DIR/bin/conda clean --all --yes

ENV PATH=$CONDA_DIR/bin:$PATH

# Install CVC5
RUN curl -L -o /tmp/cvc5.zip https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.0/cvc5-Linux-x86_64-static.zip && \
    unzip /tmp/cvc5.zip -d /tmp/cvc5 && \
    mv /tmp/cvc5/cvc5-Linux-x86_64-static/bin/cvc5 /usr/local/bin/cvc5 && \
    chmod +x /usr/local/bin/cvc5 && \
    rm -rf /tmp/cvc5 /tmp/cvc5.zip

# Copy environment.yml and install conda environment
COPY environment.yml .

RUN conda tos accept --override-channels --channel https://repo.anaconda.com/pkgs/main && \
    conda tos accept --override-channels --channel https://repo.anaconda.com/pkgs/r && \
    conda env create -f environment.yml && \
    conda clean --all --yes

# Activate environment
ENV CONDA_DEFAULT_ENV=CDMO
ENV PATH="$CONDA_DIR/envs/${CONDA_DEFAULT_ENV}/bin:$PATH"

# Copy your code
COPY . .

# Default command
CMD ["bash"]
