'''
Projet d'algorithmique des graphes
-Deltour Maxence
-Diar Dia Modou
-Makhloufi Khalil

'''
from collections import defaultdict
import heapq

import math
import numpy as np
import numpy.random as rd
import matplotlib.pyplot as plt
import time


#-------------------------------Ppvoisin-----------------------------------#


# g_to_triple: transforme le graphe G en liste de tuple(s1,s2,p)
def g_to_triple (G):
    L = []
    for i in range (0, len(G)):
        for j in range (i, len(G)):
            if (i != j):
                L.append([i+1, j+1, G[i][j]])
    return L

# takeValue : renvoie la valeur du poids dans le triplet (s1,s2,p)
def takeValue(elem):
    return elem[2]

# get_related_a: renvoie la liste des arêtes associée à s
def aretes_related(s, L_a):
    L = []
    for i in L_a:
        if i[0] == s or i[1] == s:
            L.append(i)
    return L


## Ppvoisin
def Ppvoisin ( G):
    s=s=rd.randint(1,len(G[1])+1)
    # On crée une liste contenant s
    L = [s]

    # On transforme le graphe en liste d'arêtes et on trie
    aretes = g_to_triple(G)
    aretes.sort(key = takeValue)

    # Tant qu'on est pas passés par tous les sommets
    while len(L) < len(G):
        # On récupère le dernier sommet
        last_s = L[-1]

        # On récupère les arêtes dont une des extrémités est s
        L_a = aretes_related(last_s, aretes)

        # On ajoute l'autre extremité à la liste L
        for a in L_a:
            if a[1] not in L:
                L.append(a[1])
                break
            if a[0] not in L:
                L.append(a[0])
                break

    # On retourne la liste des sommets
    return L
#-------------------------------OptimisePpVoisin--------------------------------#

def sommePoidsCycle(G,L): #calcule la somme des poids du cycle
    s = 0
    for i in range(0,len(L) - 1):
        j = i+1
        ligne = L[i] - 1
        col = L[j] -1
        s+= G[ligne][col]
    return s

def decroiserListe(lst): #renvoie le cycle dans le sens inverse
    lst.pop()
    reversed_list = lst[::-1]
    reversed_list.append(reversed_list[0])
    return reversed_list

def OptimisePpVoisin(G,L):  # si le poids du cycle est plus grand que celui de son inverse, alors renvoie
                            # son inverse sinon renvoie le cycle.
    L1=L.copy()
    CycleDécroiser = decroiserListe(L)
    LPoids = sommePoidsCycle(G,L)
    CycleDécroiserPoids = sommePoidsCycle(G,CycleDécroiser)
    if  LPoids > CycleDécroiserPoids:
        return CycleDécroiser
    return L1


#-------------------------------Arêtes de poids min-----------------------------#


# renvoie la liste de sommets L qui contient le sommet s
def list_that_contains (s, L):
    for i in L:
        if s in i:
            return i
    return None

def list_count (s,L):
    deg = 0
    for a in L:
        if s == a[0] or s == a[1]:
            deg += 1
    return deg

def Apminimum(G):
    # trier les arètes par poids croissants
    aretes = g_to_triple(G)
    aretes.sort(key = takeValue)

    L_s = [] # Liste des sommets
    L_a = [] # Liste des arêtes

    # Initialisation
    for i in range (0, len(G)):
        L_s.append([i+1])

    Lss = []
    # Pour chaque arêtes de la forme (s1,s2,p)
    for w in aretes:
        # On récupère les listes contenant s1 et s2
        l1 = list_that_contains(w[0], L_s)
        l2 = list_that_contains(w[1], L_s)

        # Si s1 et s2 dans liste différente -> union
        if (list_count (w[0],L_a) < 2) and (list_count (w[1], L_a) < 2):
            if l1 != l2:
                L_a.append(w)
                if not(w[0] in Lss):
                    Lss.append(w[0])
                if not(w[1] in Lss):
                    Lss.append(w[1])
                l1.extend(l2)
                L_s.remove(l2)

        # Si on est passés par tous les sommets
        if (len(L_a) == len(G) -1 ):
            ls = []
            for s in L_s[0]:
                if list_count(s,L_a) < 2:
                    ls.append(s)
            for ar in aretes:
                if ls[0] == ar[0] and ls[1] == ar[1] or ls[1] == ar[0] and ls[0] == ar[1]:
                    L_a.append(ar)
            break
    return Lss

#-------------------------------------Pvcprim-----------------------------------#
def prim(graphe, nb_sommets):
    premier_sommet=rd.randint(0,nb_sommets)
    acm = defaultdict(set) #arbre couvrant de poids minmum
    visited = set([premier_sommet]) 

    #construction du tas
    aretes = []
    for i in range(0,nb_sommets):
        if (graphe[premier_sommet][i] !=-1 and graphe[premier_sommet][i] !=0):
            aretes.append((graphe[premier_sommet][i],premier_sommet,i))
    heapq.heapify(aretes)

    while aretes:
        poid,premier, suivant = heapq.heappop(aretes)
        if suivant not in visited:
            visited.add(suivant)
            acm[premier].add(suivant)

            for i in range (0,nb_sommets):
                poid = graphe[suivant][i]
                if(poid !=-1 and poid !=0):
                    if i not in visited:
                        heapq.heappush(aretes, (poid,suivant, i))
    return acm

#permet de faire le parcours prefix sur l'arbre donnée sous forme de dictionnaire
def parcours_prefix_aux(acm, premier_sommet, parcours):
    parcours.append(premier_sommet)
    if premier_sommet in acm:
        for child in acm[premier_sommet]:
            parcours_prefix_aux(acm, child, parcours)
    return parcours
def parcours_prefix(acm,premier_sommet,):
    return parcours_prefix_aux(acm,premier_sommet,[])

def pvcPrim(matrice):
    nb_sommets=len(matrice[1])
    acm=dict((prim(matrice,nb_sommets)))
    p_s=list(acm.keys())[0]
    return  [x+1 for x in parcours_prefix(acm,p_s)]

#-------------------------Euristique de la demi somme: -------------------------#

# Copie la solution partielle dans la solution finale
def partielle_to_finale(chemin):
    chemin_final[:N + 1] = chemin[:]
    chemin_final[N] = chemin[0]

# Trouve le premier minorant qui se termine au sommet s
def premier_minorant(G, s):
    min = float('inf')
    for i in range (1, len(G)):
        if G[s][i] < min and i != s:
            min = G[s][i]
    return min

# Trouve le second minorant qui se termine au sommet s
def second_minorant(G, s):
    premier = float('inf')
    second = float('inf')
    for i in range (1, len(G)):
        if (i == s):
            continue
        if (G[s][i] <= premier):
            second = premier
            premier = G[s][i]
        elif (G[s][i] <= second and G[s][i] != premier):
            second = G[s][i]
    return second



def Esdemisomme_rec(G, minorant, poids, niveau, chemin, visited):
    # On déclare la variable resultat_final en global afin de l'avoir pour la récursivité
    global resultat_final

    # Si on est passés par tous les sommets
    if niveau == N:

        # S'il y a une arête entre le premier sommet et le dernier sommet
        if G[chemin[niveau - 1]][chemin[0]] != 0:
            poids_total = poids + G[chemin[niveau - 1]][chemin[0]]
            if poids_total < resultat_final:
                partielle_to_finale(chemin)
                resultat_final = poids_total
        return


    # Pour chaque autre niveau, il faut passer par tous les sommets pour
    # construire récursivement l'arbre de recherche
    for i in range(N):

        # Si le sommet n'est pas le même et qu'il n'a pas été visité
        if (G[chemin[niveau-1]][i] != 0 and visited[i] == False):
            temp = minorant
            poids += G[chemin[niveau - 1]][i]

            # Deux calculs différents pour les minorants (racine, reste)
            if niveau == 1:
                minorant -= ((premier_minorant(G, chemin[niveau - 1]) + premier_minorant(G, i)) / 2)
            else:
                minorant -= ((second_minorant(G, chemin[niveau - 1]) + premier_minorant(G, i)) / 2)

            # Si le minorant (minorant + poids) est inférieur à resultat_final,
            # on continue l'exploration
            if minorant + poids < resultat_final:
                chemin[niveau] = i
                visited[i] = True

                # Appel récursif avec niveau + 1
                Esdemisomme_rec(G, minorant, poids, niveau + 1, chemin, visited)

            # Sinon on reset le poids et le minorant
            poids -= G[chemin[niveau - 1]][i]
            minorant = temp

            # Remettre à zero visited
            visited = [False] * len(visited)
            for i in range(niveau):
                if chemin[i] != -1:
                    visited[chemin[i]] = True


def Esdemisomme(G):
    # On utilise l'heuristique de la demi-somme pour calculer le minimum
    minorant = 0
    chemin = [-1] * (N + 1)
    visited = [False] * N

    # Calcule le minorant
    for i in range(N):
        minorant += (premier_minorant(G, i) + second_minorant(G, i))

    # Arrondir le minorant en cas de besoin
    minorant = math.ceil(minorant / 2)

    # On commence au sommet 1
    visited[0] = True
    chemin[0] = 0

    # Appel à la fonction récursive avec un poids de 0 et un niveau de 1 (racine)
    Esdemisomme_rec(G, minorant, 0, 1, chemin, visited)

#------------------------------Fonctions outils --------------------------------#


#------calcul des coordonnées-----#
def coord_sommets(nb_sommets) :
    coord_sommets = []
    for i in range (0,nb_sommets):
        x=round(rd.rand(),3)
        y= round(rd.rand(),3)
        coord_sommets.append((x,y))
    return coord_sommets

#----génération de la matrice-----#

def generation_matrice(nb_sommets,coord):
    matrice = np.zeros((nb_sommets,nb_sommets))
    for i in range (0,nb_sommets):
        for j in range(0,nb_sommets):
            if(i!=j):
                matrice[i][j]=round((math.dist(coord[i],coord[j])),3)
                matrice[j][i]=round((math.dist(coord[i],coord[j])),3)
    return matrice


#-------affichage du graphe-------#
def affichage(matrice, coords, times, times2,time_pp,time_ad,time_pvc,time_edm,poids):
    fig, ax = plt.subplots(2, 4, figsize=(10,10))
    n = len(matrice)
    for i in range(n):
        x, y = coords[i]
        ax[0,0].plot(x, y, 'bo')
        ax[0,0].text(x,y+0.02,str(i+1))
        ax[0,0].set_title("Graphe généré")
    for i in range(n):
        for j in range(n):
            if matrice[i][j] != -1:
                x1, y1 = coords[i]
                x2, y2 = coords[j]
                ax[0,0].plot([x1, x2], [y1, y2], 'k--',linewidth=0.5)
    #Ajouter les barres
    
    ax[0,1].bar(['PpVoisin', 'ApMinimum', 'PvcPrim','Esdemisomme'], times)
    ax[0,1].set_title("Temps d'éxécution des fonctions")
    
    ax[0,2].bar(['PpVoisin', 'ApMinimum', 'PvcPrim'], times2)
    ax[0,2].set_title("Temps d'éxécution des fonctions pour 100 essais")
    

    ax[0,3].bar(["Apminimum","Pvcprim","Esdemisomme"], time_pp)
    ax[0,3].set_title("Pourcentage gagné de PpVoisin")

    ax[1,0].bar(["PpVoisin","PvcPrim","Esdemisomme"], time_ad)
    ax[1,0].set_title("Pourcentage gagné de Apminimum")

    ax[1,1].bar(["Ppvoisin", "Apminimum","Esdemisomme"], time_pvc)
    ax[1,1].set_title("Pourcentage gagné de PvcPrim")

    ax[1,2].bar(["Ppvoisin","Apminimum","Pvcprim"],time_edm)
    ax[1,2].set_title("Pourcentage gagné de Esdemisomme")

    ax[1,3].bar(["Ppvoisin","Apminimum","Pvcprim","Esdemisomme"],poids)
    ax[1,3].set_title("Poids des chemins générés")

    plt.show()
#--------Poid d'un chemin---------#

def poid_chemin(chemin,matrice):
    nb_s=len(chemin)
    res=0
    for i in range (nb_s-2):
        res+= matrice[chemin[i]-1][chemin[i+1]-1]
    res +=matrice[chemin[nb_s-1]-1][chemin[0]-1]
    return res

#-------------Stats--------------#
#renvoie la moyenne des poids sur 100 cycles de ppvoisin et optimisePpVoisin sur les mêmes cycles

def moyenne_long_ppvoisin(matrice):
    longueur = [None]*100
    longueur_opt= [None]*100
    nb_sommets=len(matrice[1])
    for i in range (0,100):
        longueur[i]=poid_chemin(Ppvoisin(matrice),matrice)
        longueur_opt[i]=poid_chemin(OptimisePpVoisin(matrice,(list(Ppvoisin(matrice)))),matrice)
    return np.mean(longueur),np.mean(longueur_opt)


def moyenne_long_pvc(matrice):
    longueur = [None]*100
    nb_sommets=len(matrice[1])
    for i in range (0,100):
        longueur[i]=poid_chemin(pvcPrim(matrice),matrice)
    return np.mean(longueur)

def temps_gagné(temps,funct):
    time=temps[funct]
    list=[element for i, element in enumerate(temps) if i != funct]
    res=[None]*len(list)
    for i in range(0,len(list)):
        if(time<list[i]):
            res[i]=(time / list[i]) * 100
        else:
            res[i] = -1 *(list[i]/time)*100
    return res






#----------------------------------------Main------------------------------------------#
#lecture
print("Projet d'algorithmique des graphes : ")
print("Nous vous proposons dans ce programme plusieurs solutions au problème du voyageur de commerce")
print("")

nb_sommets=int(input("Veuillez insérer le nombre de sommets du graphe ::"))
print("")


#construction de la matrice
coord = coord_sommets(nb_sommets)
matrice= generation_matrice(nb_sommets,coord)

#pour le temps:
times=[None]*4#temps d'executuion pour un seul appel
times2=[None]*3 #temps d'execution pour 100 appels
#pour les poids:
poids=[None]*4

print("----------------------------La matrice d'adjacence-----------------------------")
print("")
print(matrice)
print("")

print("----------------------------------PpVoisin-------------------------------------")
print("")

start= time.time()
#renvoie la moyenne des poids sur 100 cycles de ppvoisin et optimisePpVoisin sur les mêmes cycles
moyenne= moyenne_long_ppvoisin(matrice)
ppvoisin=Ppvoisin(matrice)
print("Cycle obtenu avec Ppvoisin ", ppvoisin)
end= time.time()
times[0]=end-start
poid_pp= poid_chemin(ppvoisin,matrice)
poids[0]=poid_pp
print("Poid :: ",poid_pp)
print("Poids moyenne des cycles sur 100 cycles : ",moyenne[0] )
end2=time.time()
times2[0]=end2-start
#optimisePpVoisin
print("-------------------------------OptimisePpVoisin--------------------------------")
print("")
s_crois=OptimisePpVoisin(matrice,ppvoisin)
print("Cycle obtenu après avoir défait les croisements : ",s_crois)
poid_decr= poid_chemin(s_crois,matrice)
poids[1]= poid_chemin(s_crois,matrice)
print("poid :: ",poid_decr)
print("Poids moyenne des cycles sur les 100 cycles obtenus par ppVoisin : ", moyenne[1])

print("----------------------------------ApMinimum------------------------------------")
print("")
start= time.time()
apmin=Apminimum(matrice)
end= time.time()
times[1]=end-start

poid_ap=poid_chemin(apmin,matrice)
poids[1]=poid_ap
print ("Cycle obtenu avec ApMinimum : ", apmin)
print("Poid :: ",poid_ap)
end2=time.time()
times2[1]=end2-start


#pvc
print("-----------------------------------PvcPrim-------------------------------------")
print("")
start= time.time()
pvc= pvcPrim(matrice)
poid_pvc=  poid_chemin(pvc,matrice)
poids[2]=poid_pvc
print("Cycle obtenu avec pvcPrim :: " ,pvc)
end= time.time()
times[2]=end-start
print("Poid :: ",poid_pvc)
print("Poids moyenne des cycles sur 100 cycles : ", moyenne_long_pvc(matrice))
end2=time.time()
times2[2]=end2-start

print("-----------------------------------Esdemisomme-------------------------------------")
#initialisation
N = len(matrice)
chemin_final = [None] * (N + 1)
visited = [False] * N
resultat_final = float('inf')
start= time.time()
Esdemisomme(matrice)
end= time.time()
poids[3]=resultat_final
print("Cycle obtenu avec Esdemisomme :: " , end = ' ')
for i in range(N ):
    print(chemin_final[i]+1, end = ' ')
print()
print("Poid :", resultat_final)

times[3]=end-start

#temps gangé
time_pp=temps_gagné(times,0)
time_ap=temps_gagné(times,1)
time_pvc=temps_gagné(times,2)
time_edm=temps_gagné(times,3)

#affichage
print("\nRéalisé par : \n-Makhloufi Khalil \n-Deltour Maxence \n-Diar Dia Modou ")

affichage(matrice,coord,times,times2,time_pp,time_ap,time_pvc,time_edm,poids)




