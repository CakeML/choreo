FROM agomezl/cakeml

RUN mkdir bakery/
COPY --chown=agomezl . bakery/

RUN cd bakery/semantics && Holmake
RUN cd bakery/semantics/proofs && Holmake
