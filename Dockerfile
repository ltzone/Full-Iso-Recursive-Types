FROM coqorg/coq:8.13.2 AS lngen
RUN sudo apt update \
    && sudo apt upgrade -y \
    && sudo apt install haskell-stack -y \
    && sudo apt clean \
    && git clone --depth=1 https://github.com/plclub/lngen \
    && cd lngen \
    && stack install \
    && cd .. \
    && rm -rf lngen


FROM coqorg/coq:8.13.2
RUN git clone --depth=1 -b coq8.10 https://github.com/plclub/metalib \
    && cd metalib/Metalib \
    && make install \
    && cd ../.. \
    && rm -rf metalib \
    && git clone --depth=1 https://github.com/sweirich/ott -b ln-close \
    && cd ott \
    && opam pin add ott . -y \
    && opam pin add coq-ott . -y \
    && cd .. \
    && rm -rf ott \
    && rm -rf /home/coq/.opam/4.07.1+flambda/.opam-switch/build
WORKDIR /home/fulliso
COPY --from=lngen /home/coq/.local/bin/lngen /home/coq/.local/bin/lngen
COPY --chown=coq ./ ./
CMD /bin/bash
