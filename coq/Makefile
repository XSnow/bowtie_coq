################################################################################
#                                                                              #
#   Makefile                                                                   #
#   Xuejing Huang 2021                                                         #
#   Distributed under the terms of the GPL-v3 license                          #
#                                                                              #
#   This file is part of DistributingTypes.                                    #
#                                                                              #
#   DistributingTypes is free software: you can redistribute it and/or modify  #
#   it under the terms of the GNU General Public License as published by       #
#   the Free Software Foundation, either version 3 of the License, or          #
#   (at your option) any later version.                                        #
#                                                                              #
#   DistributingTypes is distributed in the hope that it will be useful,       #
#   but WITHOUT ANY WARRANTY; without even the implied warranty of             #
#   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the              #
#   GNU General Public License for more details.                               #
#                                                                              #
#   You should have received a copy of the GNU General Public License          #
#   along with DistributingTypes.  If not, see <https://www.gnu.org/licenses/>.#
#                                                                              #
################################################################################

OTT_LOC    = ../spec
LNGEN = lngen #$(stack exec lngen)

## Name of the submakefile generated by coq_makefile
COQMKFILENAME=CoqSrc.mk

LIBNAME="Top"

OTTFILE=rules

FILES    = Definitions LN_Lemmas
VFILES   = $(foreach i, $(FILES), $(i).v)
VOFILES  = $(foreach i, $(FILES), $(i).vo)


.PHONY: clean

.SECONDARY: $(VFILES)

all: coq

coq: $(COQMKFILENAME) $(VOFILES)
	@$(MAKE) -f CoqSrc.mk

%.vo: %.v $(COQMKFILENAME)
	@$(MAKE) -f $(COQMKFILENAME) $*.vo

Definitions.v: $(OTT_LOC)/$(OTTFILE).ott
	ott $(OTT_LOC)/$(OTTFILE).ott -o Definitions.v -coq_lngen true -coq_expand_list_types true
	@if grep '<<no parses (' $@ >/dev/null 2>&1 && \
	[ -z "$(DONTSTOP)" ]; then \
		echo; \
	echo "***** OTT PARSE ERROR(S) *****"; \
		grep -n '<<no parses (' $@; \
		$(RM) $@; \
		exit 1; \
	fi >&2
	sed -i '1iSet Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".\n' Definitions.v

LN_Lemmas.v: $(OTT_LOC)/$(OTTFILE).ott
	$(LNGEN) --coq LN_Lemmas.v --coq-ott Definitions $(OTT_LOC)/$(OTTFILE).ott
	sed -i '1iSet Warnings "-non-recursive,-deprecated-hint-without-locality,-deprecated,-fragile-hint-constr".\n' LN_Lemmas.v

$(COQMKFILENAME): Makefile Definitions.v
	coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o $(COQMKFILENAME)


clean:
	rm -f .*.d *.conf .*.aux *.v-e *.v.d *.vo *vio *.vos *.vok *.glob $(COQMKFILENAME) .lia.cache
