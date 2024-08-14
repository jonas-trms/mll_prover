# MLL Prover
Un assistant de preuve interactif pour le fragment multiplicatif MLL de la logique linéaire.

# Utilisation
## Changer l'entrée
Pour prouver un séquent, il faut le définir à la fin du code de la même manière que nos exemples. Il faut  ensuite modifier la dernière ligne du code, en y mettant le séquent en question: ```let _ = prove_sequent [à modifier];;```

## Définir un séquent
Un séquent est une liste OCaml de formules, et les formules sont représentées par le type suivant: ```type formula = A of int | NA of int | P of formula * formula | T of formula * formula```.

```A``` correspond à un atome, ```NA``` à un atome nié, ```P```  un  par, et ```T``` à un tenseur.

## Exécution
La boucle d'interaction se lance en exécutant le code OCaml :
```ocaml code.ml```

## Boucle d'interaction
L'utilisateur est guidé pas à pas par notre code, qui lui affiche au fur et à mesure des indications. 

À chaque étape, du pseudo-code LaTeX représentant la preuve partielle est affiché. L'utilisateur donne d'abord un entier, désignant le trou sur lequel il souhaite travailler. Les trous sont numérotés de gauche à droite dans l'arbre, et les indices commencent à 1.

Un séquent, lié à $\Sigma_1$, est alors affiché. Il contient les choix possibles pour le trou. Certaines formules, liée à $\Sigma_0$, y sont surlignées par les caractères ```<>```. L'utilisateur choisit la règle qu'il veut appliquer donnant un entier, désignant une sous-formule dans le séquent. Les formules sont indicées de de gauche à droite, toujours à partir de 1.

Des autocomplétions permettent parfois de sauter certaines de ces étapes, mais cela est toujours précisé par des messages d'information. De même, certains cas d'erreurs font parfois revenir l'utilisateur en arrière.

Si la preuve aboutit, son code LaTeX est affiché, et peut être utilisé avec le module ```ebproof```.