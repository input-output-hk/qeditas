#!/bin/bash
latex qeditastechdoc
bibtex qeditastechdoc
makeindex qeditastechdoc
latex qeditastechdoc
latex qeditastechdoc
dvipdf qeditastechdoc
