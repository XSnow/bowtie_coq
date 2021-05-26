OTT_OPTS  = -tex_show_meta false
OTT_FILES  = ../spec/rules.ott

MAIN = paper

RULESFILE = ott-rules.tex

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex $(RULESFILE)
	ott -i $(OTT_FILES) -tex_filter $(MAIN).tex $(MAIN).mng
	@pdflatex $(@:.pdf=.mng)

$(RULESFILE): $(OTT_FILES)
	ott -tex_wrap false $(OTT_OPTS) -o $@ $^
	@if grep '<<no parses (' $@ >/dev/null 2>&1 && \
		[ -z "$(DONTSTOP)" ]; then \
			echo; \
			echo "***** OTT PARSE ERROR(S) *****"; \
			grep -n '<<no parses (' $@; \
			$(RM) $@; \
			exit 1; \
	fi >&2

clean:
	@rm -f $(MAIN).pdf $(RULESFILE) *.bbl  *.aux *.fls *.out *.synctex.gz *.log *.fdb_latexmk *.blg bundle.tar.gz

.PHONY: all clean

deep_clean: clean
	@rm $(MAIN).mng
