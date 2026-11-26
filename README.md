# GEP Itinéraires — Guidage Expert Pilotage

Appli web installable (téléphone et tablette) pour préparer et suivre des itinéraires de convoi exceptionnel.
Aucun serveur, aucun compte, aucune clé : l'appli lit directement les données publiques gratuites.

## Fonctions
- Carte IGN avec les réseaux TE du Géoportail (1TE, 2TE48, TE72, TE94, TE120), ouvrages d'art et passages à niveau.
- Tracé point par point : aimant réseau TE (le tracé suit les tronçons TE choisis), liaison routière IGN, ou ligne droite.
- Profil du convoi (longueur, largeur, hauteur, poids, marge) → catégorie et vitesses (arrêté du 4 mai 2006).
- Analyse du tracé : franchissements TE et leurs restrictions, hauteurs et tonnages OpenStreetMap, mes propres mesures,
  part du trajet sur chaque réseau TE et portions hors réseau, prescriptions des gestionnaires liées aux tronçons parcourus,
  profil en long et pentes (RGE ALTI).
- Restrictions d'horaire par ville (contour de la commune) avec alerte vocale à l'approche et à l'entrée ;
  création en un geste depuis une prescription qui mentionne des horaires.
- Guidage GPS sur le tracé, sans recalcul, annonces vocales des indications et des ouvrages, vitesse limite de la catégorie,
  alerte hors tracé, écran maintenu allumé ; mode simulation pour tester.
- Enregistrement de trajet, import / export GPX, partage par lien et QR code, dossiers, feuille de route imprimable,
  sauvegarde / restauration de toutes les données.

## Sources
- IGN Géoplateforme (data.geopf.fr) : WMTS (fonds et réseaux TE), WFS `SECUROUT.TE:*` (tronçons, franchissements,
  prescriptions et liens), itinéraire, altimétrie, géocodage.
- geo.api.gouv.fr : communes et contours. OpenStreetMap / Overpass : maxheight, maxweight, maxwidth.

Outil d'aide sans valeur légale : l'arrêté d'autorisation et la reconnaissance du terrain font foi.

## Mise en ligne
Ce sont des fichiers statiques : n'importe quel hébergement HTTPS convient (GitHub Pages, Netlify…).
Le GPS et l'installation demandent une adresse en https.
