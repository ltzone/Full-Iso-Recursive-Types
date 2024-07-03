FROM coqorg/coq:8.13.2
RUN git clone --depth=1 -b coq8.10 https://github.com/plclub/metalib \
    && cd metalib/Metalib \
    && make install \
    && cd ../.. \
    && rm -rf metalib \
    && sudo apt update \
    && sudo apt upgrade -y \
    && sudo apt install haskell-stack -y \
    && sudo apt clean \
    && git clone --depth=1 https://github.com/plclub/lngen \
    && cd lngen \
    && stack install \
    && cd .. \
    && rm -rf lngen \
    && git clone --depth=1 https://github.com/sweirich/ott -b ln-close \
    && cd ott \
    && opam pin add ott . -y \
    && opam pin add coq-ott . -y \
    && cd .. \
    && rm -rf ott
WORKDIR /home/fulliso
COPY --chown=coq cast_main ./cast_main
COPY --chown=coq cast_sub ./cast_sub
CMD /bin/bash
