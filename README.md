# Markov Studio

Application de bureau **d'analyse des chaînes de Markov** à temps discret, écrite en
**R de base + tcltk**. Aucun paquet CRAN n'est requis.

```bash
Rscript MarkovStudio.R
# ou, depuis R :  source("MarkovStudio.R")
```

## Moteur mathématique

- Représentation **creuse** de la matrice de transition (triplets + CSR) : traitements
  en O(n + |E|), utilisables pour des chaînes de plusieurs milliers d'états
- **Classes de communication** (Tarjan, composantes fortement connexes), nature des
  classes (récurrente ou transitoire) et **période**
- **Loi stationnaire** (méthode de la puissance), puissances de matrice
- **Absorption** : probabilités et temps moyens d'absorption
- **Métriques spectrales**
- **Prévision** de la distribution à n pas

## Interface

- Saisie robuste d'une matrice n × n (normalisation des lignes), import et export CSV,
  enregistrement et chargement
- Graphe des transitions (vue complète et vue par classes), heatmap réorganisée par classe
- Courbe de prévision, export PNG de la vue courante
- Tests intégrés (`.run_tests`)

Prérequis : R compilé avec le support Tcl/Tk (`capabilities("tcltk")`).
