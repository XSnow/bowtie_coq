OTT = ott
OTT_FLAGS := -signal_parse_errors true -show_defns false
OTT_CHK_FLAGS := -show_sort true -show_defns true

NAME = rules

.PHONY: clean

all: $(NAME)_included.tex test

check: $(NAME)_check

test: $(NAME)_test.pdf

%.pdf : %.tex
	pdflatex $<

%_included.tex : %.ott
	$(OTT) $(OTT_FLAGS) -tex_wrap false -o $@ $<

%_test.tex : %.ott
	$(OTT) $(OTT_FLAGS) -o $@ $<

%_check : %.ott
	$(OTT) $(OTT_CHK_FLAGS) -i $<

# including all tex with _ in its name
clean:
	rm -f *.aux *.log *_*.tex *.bbl *.blg *.pdf
