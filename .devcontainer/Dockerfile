ARG ISABELLE_IMAGE=makarius/isabelle:Isabelle2026_ARM
FROM ${ISABELLE_IMAGE}

USER root
RUN apt-get update \
    && apt-get install -y --no-install-recommends ca-certificates git python3 g++ libgmp-dev \
    && rm -rf /var/lib/apt/lists/*

ENV PATH="/home/isabelle/Isabelle/bin:${PATH}"
USER isabelle
