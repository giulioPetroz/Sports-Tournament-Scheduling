FROM ubuntu:22.04

WORKDIR /cdmo

# Install dependencies
RUN apt-get update && \
    DEBIAN_FRONTEND=noninteractive apt-get install -y \
    curl bzip2 git z3 cvc5 && \
    apt-get clean && rm -rf /var/lib/apt/lists/*

# Install Miniconda
ENV CONDA_DIR=/opt/conda
RUN curl -LO "https://repo.anaconda.com/miniconda/Miniconda3-latest-Linux-x86_64.sh" && \
    bash Miniconda3-latest-Linux-x86_64.sh -b -p $CONDA_DIR && \
    rm Miniconda3-latest-Linux-x86_64.sh && \
    $CONDA_DIR/bin/conda clean --all --yes

ENV PATH=$CONDA_DIR/bin:$PATH

# Copy environment.yml and install env
COPY environment.yml .
RUN conda env create -f environment.yml && conda clean --all --yes

ENV CONDA_DEFAULT_ENV=CDMO
ENV PATH="$CONDA_DIR/envs/${CONDA_DEFAULT_ENV}/bin:$PATH"

# Copy your code
COPY . .

# Default
CMD ["bash"]
