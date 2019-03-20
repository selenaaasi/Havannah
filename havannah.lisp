;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;                                                                                                ;;;;;
;;;;;                                       INFERENCE ENGINE                                         ;;;;;
;;;;;                                                                                                ;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; POMOCNE FUNKCIJE

;; provera da li je parametar s izvorna promenljiva (simbol koji pocinje sa ?)
(defun true-var? (s) 
  (if (symbolp s)
      (equal #\? (char (symbol-name s) 0))
    nil))

;; provera da li je parametar s promenljiva (simbol koji pocinje sa ? ili %)
(defun var? (s) 
  (if (symbolp s)
      (let ((c (char (symbol-name s) 0)))
        (or (equal c #\?) (equal c #\%)))
    nil))

;; provera da li je parametar s funkcija (simbol koji pocinje sa =)
(defun func? (s) 
  (if (symbolp s)
      (equal #\= (char (symbol-name s) 0))
    nil))

;; provera da li je parametar s predefinisani predikat (simbol koji pocinje sa !)
(defun predefined-predicate? (s)
  (if (symbolp s)
      (equal #\! (char (symbol-name s) 0))
    nil))

;; provera da li je parametar s konstanta (ako nije promenljiva ili funkcija onda je konstanta)
(defun const? (s)
  (not (or (var? s) (func? s))))

;; rekurzivna provera da li je parametar f funkcija od parametra x
(defun func-of (f x)
  (cond
   ((null f) ; kraj rekurzije
    t)
   ((atom f)
    (equal f x))
   (t
    (or (func-of (car f) x) (func-of (cdr f) x)))))

;; provera da li funkcija f ima promenljivih
(defun has-var (f)
  (cond
   ((null f) 
    nil)
   ((atom f)
    (var? f))
   (t
    (or (has-var (car f)) (has-var (cdr f))))))

;; funkcija koja vraca konsekvencu pravila
(defun rule-consequence (r)
  (car (last r)))

;; funkcija koja vraca premisu pravila
(defun rule-premises (r)
  (let ((p (cadr r)))
    (if (and (listp p) (equal (car p) 'and))
        (cdr p)
      (list p))))
      
;; funkcija koja vrsi prebacivanje upita u interni format (izbacuje 'and)
(defun format-query (q)
  (if (and (listp q) (equal (car q) 'and))
      (cdr q)
    (list q)))
    
;; izracunavanje istinitosne vrednosti predefinisanog predikata
(defun evaluate-predicate (p ls)
  (if (has-var p) nil  ; ako poseduje slobodne promenljive vraca nil (nije validna situacija)
    (if (eval p) 
        (list ls) ; ako predikat vazi vraca ulaznu listu smena
      nil))) ; u suprotnom vraca nil

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; INTERFEJSNE FUNKCIJE I GLOBALNE PROMENLJIVE

(defparameter *FACTS* nil)
(defparameter *RULES* nil)
(defparameter *MAXDEPTH* 10)

;; priprema *FACTS*, *RULES* i *MAXDEPTH*
(defun prepare-knowledge (lr lf maxdepth)
  (setq *FACTS* lf *RULES* (fix-rules lr) *MAXDEPTH* maxdepth))

;; vraca broj rezulata izvodjenja
(defun count-results (q)
  (length (infer- (format-query q) '(nil) 0)))

;; vraca listu lista smena
(defun infer (q)
  (filter-results (infer- (format-query q) '(nil) 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; FUNKCIJE KOJE VRSE DODELU NOVIH JEDINSTVENIH PROMENLJIVIH PRAVILIMA

(defun fix-rules (lr)
  (if (null lr) nil
    (cons (fix-rule (car lr)) (fix-rules (cdr lr)))))

(defun fix-rule (r)
  (let ((ls (make-rule-ls r nil)))
    (apply-ls r ls)))

(defun make-rule-ls (r ls)
  (cond
   ((null r)
    ls)
   ((var? r)
    (let ((a (assoc r ls)))
      (if (null a)
          (cons (list r (gensym "%")) ls)
        ls)))
   ((atom r)
    ls)   
   (t
    (make-rule-ls (cdr r) 
                  (make-rule-ls (car r) ls)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; FUNKCIJE KOJE VRSE PRIPREMU REZULTATA (IZBACUJU SMENE KOJE SE ODNOSE NA INTERNE PROMENLJIVE)

(defun filter-results (lls)
  (if (null lls) nil
    (cons (filter-result (car lls)) (filter-results (cdr lls)))))

(defun filter-result (ls)
  (if (null ls) nil
    (if (true-var? (caar ls))
        (cons (car ls) (filter-result (cdr ls)))
      (filter-result (cdr ls)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; FUNKCIJE KOJE SE KORISTE U IZVODJENJU

;; glavna funkcija za izvodjenje, vraca listu lista smena
;; lq - predikati upita
;; lls - lista listi smena (inicijalno lista koja sadrzi nil)
;; depth - tekuca dubina (inicijalno 0)
(defun infer- (lq lls depth)
  (if (null lq) lls
    (let ((lls-n (infer-q (car lq) lls depth)))
      (if (null lls-n) nil
        (infer- (cdr lq) lls-n depth)))))

;; izvodjenje za jedan predikat iz upita, vraca listu lista smena
(defun infer-q (q lls depth)
  (if (null lls) nil
    (let ((lls-n (infer-q-ls q (car lls) depth)))
      (if (null lls-n)
          (infer-q q (cdr lls) depth)
        (append lls-n (infer-q q (cdr lls) depth))))))

;; izvodjenje za jedan predikat sa jednom listom smena, vraca listu lista smena
(defun infer-q-ls (q ls depth)
  (if (predefined-predicate? (car q))
      (evaluate-predicate (apply-ls q ls) ls)
    (if (< depth *MAXDEPTH*)
        (append (infer-q-ls-lf q *FACTS* ls) (infer-q-ls-lr q *RULES* ls depth))
      (infer-q-ls-lf q *FACTS* ls))))
      
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; izvodjenje nad bazom cinjenica lf, vraca listu lista smena
(defun infer-q-ls-lf (q lf ls)
  (if (null lf) nil
    (let ((ls-n (infer-q-ls-f q (car lf) ls)))
      (if (null ls-n)
          (infer-q-ls-lf q (cdr lf) ls)
        (if (null (car ls-n)) ls-n
          (append ls-n (infer-q-ls-lf q (cdr lf) ls)))))))

;; izvodjenje sa jednom cinjenicom, vraca listu sa listom smena
(defun infer-q-ls-f (q f ls)
  (if (= (length q) (length f)) ; provera na istu duzinu
      (infer-q-ls-f- q f ls)
    nil))

;; izvodjenje sa jednom cinjenicom, vraca listu sa listom smena
(defun infer-q-ls-f- (q f ls)
  (if (null q) (list ls)
    (let ((nq (apply-and-eval (car q) ls)) (nf (car f)))
      (if (var? nq) 
          (infer-q-ls-f- (cdr q) (cdr f) (append ls (list (list nq nf))))
        (if (equal nq nf) 
            (infer-q-ls-f- (cdr q) (cdr f) ls)
          nil)))))
          
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; izvodjenje nad bazom pravila, vraca listu lista smena
(defun infer-q-ls-lr (q lr ls depth)
  (if (null lr) nil
    (let ((ls-n (infer-q-ls-r q (car lr) ls depth)))
      (if (null ls-n)
          (infer-q-ls-lr q (cdr lr) ls depth)
        (if (null (car ls-n)) ls-n
          (append ls-n (infer-q-ls-lr q (cdr lr) ls depth)))))))

;; izvodjenje sa jednim pravilom, vraca listu sa listom smena
(defun infer-q-ls-r (q r ls depth)
  (let ((c (rule-consequence r)))
    (if (= (length q) (length c))
        (let ((lsc (unify q c nil ls)))
          (if (null lsc) nil
            (infer- (apply-ls (rule-premises r) (car lsc)) (cdr lsc) (1+ depth))))
      nil)))

;; unifikacija predikata upita q i konsekvence pravila c primenom liste smena ls, vraca listu smena
(defun unify (q c uls ls)
  (if (or (null q) (null c))
      (if (and (null q) (null c)) (list uls ls) nil)
    (let ((eq (car q)) (ec (car c)))
      (cond
       ((equal eq ec)
        (unify (cdr q) (cdr c) uls ls))
       ((var? eq)
        (cond
         ((var? ec)
          (let ((a (assoc ec uls)))
            (cond
             ((null a)              
              (unify (cdr q) (cdr c) (cons (list ec eq) uls) ls))
             ((equal (cadr a) eq)
              (unify (cdr q) (cdr c) uls ls))
             (t
              nil))))
         ((func? ec)
          nil)
         (t ;; const
          (let ((a (assoc eq ls)))
            (cond
             ((null a)
              (unify (cdr q) (cdr c) uls (cons (list eq ec) ls)))
             ((equal (cadr a) ec)
              (unify (cdr q) (cdr c) uls ls))
             (t 
              nil))))))
       ((func? eq)
        (cond
         ((var? ec)
          (if (func-of eq ec) nil
            (let ((a (assoc ec uls)))
              (cond
               ((null a)              
                (unify (cdr q) (cdr c) (cons (list ec eq) uls) ls))
               ((equal (cadr a) eq)
                (unify (cdr q) (cdr c) uls ls))
               (t
                nil)))))
         ((func? ec)
          nil)
         (t ;; const
          (let ((f (apply-ls eq ls)))
            (if (has-var f) nil
              (if (equal (eval f) ec)
                  (unify (cdr q) (cdr c) uls ls)
                nil))))))
       (t ;; const
        (cond
         ((var? ec)
          (let ((a (assoc ec uls)))
            (cond
             ((null a)              
              (unify (cdr q) (cdr c) (cons (list ec eq) uls) ls))
             ((equal (cadr a) eq)
              (unify (cdr q) (cdr c) uls ls))
             (t
              nil))))
         (t ;; func or const
          nil)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; PRIMENA LISTE SMENA I IZRACUNAVANJE IZRAZA

(defun apply-and-eval (x ls)
  (if (var? x)
      (apply-ls x ls)
    (if (and (listp x) (func? (car x)))
        (eval (apply-ls x ls)) 
      x)))

;; primena liste smena ls na izraz x
(defun apply-ls (x ls)
  (cond
   ((null x)
    x)
   ((var? x)
    (let ((ax (assoc x ls)))
      (if (null ax) x
        (cadr ax))))
   ((atom x)
    x)
   (t
    (cons (apply-ls (car x) ls) (apply-ls (cdr x) ls)))))



(defun pocni_igru() ;;jedina funkcija koja se direktno zove iz projekta,enkapsulira sve ostale funkcionalnosti igre

    (inicijalizuj)
    (prikazi_celu_tablu)
    
    (igraj)
)
(defun inicijalizuj() ;;vrsi inicijalizaciju svih vrednosti potrebnih za pocetak igre

    (print "Unesi velicinu table:")
    (setq velicina_table (read)) ;;velicina tabele koju unosi igrac

    (setq nn (- (* 3 velicina_table) 1))
    (setq mm (1- (* 2 velicina_table)))
    (setq lista_slova '((A 0) (B 1) (C 2) (D 3) (E 4) (F 5) (G 6) (H 7) (I 8) (J 9) (K 10) (L 11) (M 12) (N 13) (O 14) (P 15) (Q 16) (R 17) (S 18) (T 19) (U 20) (V 21) (W 22) (X 23) (Y 24) (Z 25)))
    (setq lista_za_igru (generisi_slovca (1+ (* 2 (1- velicina_table))) lista_slova)) ;;postavlja vrednosti liste_za_igru koja je oblika '((A 0) (B 1))..) na potrebne vrednosti,
    ;;u zavisnosti od velicine table,lista slova je uvek sastavljena od svih slova engleskog alfabeta
    (setq konacna_lista (generisi_pomeraje velicina_table lista_za_igru)) ;;postavlja vrednosti liste konacna_lista koja je oblika '((A 0 5) (B 1 4)) koja pored prva dva elementa svake podliste
                                                                         ;koji su isti kao kod liste za igru ima i dodatni parametar,pomeraj,potreban za validno prevodjenje poteza
    (setq lista_nedozvoljenih (generisi_nedozvoljene konacna_lista 0 (1- velicina_table)));;postavlja vrednosti liste lista_nedozvoljenih koja je tipa '((A 0 5) (B 0 6)) gde nakon prvog elementa
                                                                                          ;;svake podliste koji je odgovarajuce slovo,slede redom donja i gornja granica (kolona) za poteze koje je moguce odigrati za odgovarajuce slovo
    (setq fork '()) ;;da li je kreiran fork
    (setq prsten '());;da li je kreiran prsten
    (setq most '()) ;; da li je kreiran
    (setq stanje (generisi_stanje velicina_table 0 (1- velicina_table) velicina_table)) ;;postavlja pocetno stanje igre(praznu tablu),u zavisnosti od velicine table,pozivom funkcije generisi_stanje
    (setq minValue (cons stanje (list -1000)))
    (setq maxValue (cons stanje (list 1000)))
    (setq lista_temena  (nadji_temena stanje)) 
    (setq pomocna_potez (ko_igra_prvi))  ;;ko_igra_prvi vraca listu tipa '(X 0) ili '(O X) u zavisnosti od toga da li korisnik izabere da igra prvi potez,gde prvi simbol odgovara coveku,a drugi masini
    ;;(setq minORab (biraj_trazenje))
    (setq simbol_prvi_igrac (car pomocna_potez)) ;;postavlja simbol_covek na odgovarajuci element liste pomocna_potez
    (setq simbol_drugi_igrac (car (cdr pomocna_potez))) ;;postavlja simbol_masina na odgovarajuci element liste pomocna_potez
    (setq moja_lista (generisi_f konacna_lista (- velicina_table 1) 0) );;5 je velicina table -1
    (setq faktor 0)
    (setq dubina 2)
    (setq delilacfaktora (prebrojivalidna stanje))
    (setq pomocnacetridva '())
;;      (setq stanje '((0 (0 -1) (1 -1) (2 -1) (3 0) (4 0) (5 0) (6 0) (7 -1) (8 -1) (9 -1))
;;  (1 (0 -1) (1 -1) (2 0) (3 0) (4 0) (5 0) (6 0) (7 -1) (8 -1) (9 -1))
;;  (2 (0 -1) (1 0) (2 0) (3 0) (4 X) (5 0) (6 0) (7 -1) (8 -1) (9 -1))
;;  (3 (0 0) (1 0) (2 0) (3 0) (4 0) (5 0) (6 0) (7 -1) (8 -1) (9 -1))
;;  (4 (0 -1) (1 0) (2 0) (3 0) (4 0) (5 O) (6 0) (7 -1) (8 -1) (9 -1))
;;  (5 (0 -1) (1 -1) (2 0) (3 0) (4 X) (5 0) (6 0) (7 -1) (8 -1) (9 -1))
;;  (6 (0 -1) (1 -1) (2 -1) (3 0) (4 0) (5 0) (6 0) (7 -1) (8 -1) (9 -1))))
    (print stanje)
  
)
(defun prebrojivalidna(stanje)
    (cond 
        (
            (null stanje)
            0
        )
        (t
            (+ (prebrojivalidnavrsta (cdr (car stanje))) (prebrojivalidna (cdr stanje)))
        )
    )
)
(defun prebrojivalidnavrsta(lista)
    (cond 
        (
            (null lista)
            0
        )
        (
            (= (car (cdr (car lista))) 0)
            (1+ (prebrojivalidnavrsta(cdr lista)))
        )
        (t 
            (prebrojivalidnavrsta(cdr lista))
        )
    )
)
(defun povecajfaktor()
    (setq faktor (+ faktor (/ 1.0 delilacfaktora)))
    (proveridubinu)
    (print faktor)
    (print dubina)
)
(defun proveridubinu()
    (cond 
        (
            (> faktor 0.75)
            (setq dubina 4)
        )
        (
            (> faktor 0.5)
            (setq dubina 3)
        )
    )
)
;;PROVERA ZA PRSTEN START ~~~ 
;; DISJUNKTNI START
(defun nadji_put_d_prsten (l cvorovi put_d)
    (cond 
        ((null l) cvorovi)
        (t
            (let*
                (
                  (cvorovi1 (append cvorovi (list (car l))))
                ;;   (potomci1 (dodaj_potomke_bfs (car l) (append (cdr l) cvorovi1) simbol))
                  (potomci1 (dodaj_potomke_prsten (car l) (append cvorovi (cdr l)) put_d))
                  (l1 (append (cdr l) potomci1))
                )
                (nadji_put_d_prsten l1 cvorovi1 put_d)
            )
        )
    )
)
(defun dodaj_potomke_prsten(cvor obradjeni put_d)
    (let*
        (
            (p1 (cons (+ (car cvor) 0) (list (+ (cadr cvor) 1)) )  )
            (p11 (if (proveri_element_p p1 put_d) p1 '() ) )

            (p2 (cons (+ (car cvor) 1) (list (+ (cadr cvor) 1)) )  )
            (p22 (if (proveri_element_p p2 put_d) p2 '() ) )
            
            (p3 (cons (+ (car cvor) 1) (list (+ (cadr cvor) 0)) )  )
            (p33 (if (proveri_element_p p3 put_d) p3 '() ) )
           
            (p4 (cons (+ (car cvor) 1) (list (- (cadr cvor) 1)) )  )
            (p44 (if (proveri_element_p p4 put_d) p4 '() ) )
           
            (p5 (cons (+ (car cvor) 0) (list (- (cadr cvor) 1)) )  )
            (p55 (if (proveri_element_p p5 put_d) p5 '() ) )
          
            (p6 (cons (- (car cvor) 1) (list (- (cadr cvor) 1)) )  )
            (p66 (if (proveri_element_p p6 put_d) p6 '() ) )
         
            (p7 (cons (- (car cvor) 1) (list (- (cadr cvor) 0)) )  )
            (p77 (if (proveri_element_p p7 put_d) p7 '() ) )
         
            (p8 (cons (- (car cvor) 1) (list (+ (cadr cvor) 1)) )  )
            (p88 (if (proveri_element_p p8 put_d) p8 '() ) )
          
            (susedi (izbaci_nil (npl8 p44 p55 p11 p22 p33 p66 p77 p88)))

        )
        (proveri_obradjene_p susedi obradjeni)
    )
)
(defun izbaci_nil (lista)
    (cond
        (
            (null lista)
            '()
        )
        (
            (equal nil (car lista))
            (izbaci_nil (cdr lista))
        )
        (
            t (cons (car lista) (izbaci_nil (cdr lista)))
        )
    )
)
(defun npl8 (c1 c2 c3 c4 c5 c6 c7 c8) ;; napravi listu od 8 cvora 
    (append (append (cons c1 (list c2)) (cons c3 (list c4)) ) (append (cons c5 (list c6)) (cons c7 (list c8))) )
)
;;DISJNUKTNI END
(defun nadji_presek (lista1 lista2)
    (cond
        (
            (null lista1)
            '()
        )
        (
            (proveri_element_p (car lista1) lista2)
            (cons (car lista1)(nadji_presek (cdr lista1) lista2))
        )
        (
            t
            (nadji_presek (cdr lista1) lista2)
        )
    )
)

(defun nadji_put_izmedju_i1_i2 (g_ivica3 d_ivica3 put_d ) 
    (let*
        (
            ;;start je gornja ivica1
            (start (list (cadr g_ivica3)))
            ;;cilj je donja ivica2
            (cilj (caddr d_ivica3))
            ;;lista za izbacivanje iz puta su gornje cvor i ivica2 i donje cvor i ivica1, da slucajno preko njih ne bi dosli do ivica2
            (izbaci (append (cons (car g_ivica3) (list (caddr g_ivica3))) (cons (car d_ivica3) (list (cadr d_ivica3))))  )
            ;; proveri_obradjenje_p izbacuje iz put_p one koji se nalaze u listi izbaci
            (put (proveri_obradjene_p put_d izbaci))

        )
        (proveri_obradjene_p (nadji_put_d_prsten start '() put) start)
    )
)
(defun nadji_put_izmedju_i2_i1 (g_ivica3 d_ivica3 put_d ) 
    (let*
        (
            ;;start je gornja ivica2
            (start (list (caddr g_ivica3)))
            ;;cilj je donja ivica1
            (cilj (cadr d_ivica3))
            ;;izbacuje gornje cvor i ivica1 i donje cvor i ivica2, da slucajno preko njih ne bi dosli do ivica1
            (izbaci (append (cons (car g_ivica3) (list (cadr g_ivica3))) (cons (car d_ivica3) (list (caddr d_ivica3))))  )
            ;; proveri_obradjenje_p izbacuje iz put_p one koji se nalaze u listi izbaci
            (put (proveri_obradjene_p put_d izbaci))

        )
        (proveri_obradjene_p (nadji_put_d_prsten start '() put) start) 
    )
)
(defun proveri_obradjene_p(cvorovi obradjeni) ;; ako se neki iz cvorovi nalazi u obradjeni izbacuje ih
    (cond 
        (
            (null cvorovi)
            '()
        )
        (
            (not (proveri_element_p (car cvorovi) obradjeni))
            (cons (car cvorovi) (proveri_obradjene_p (cdr cvorovi) obradjeni))
        )
        (
            t (proveri_obradjene_p (cdr cvorovi) obradjeni)
        )

    )
)
(defun proveri_element_p (el lista)
    (cond 
        (
            (null lista)
            '()
        )
        (
            (equal el (car lista))
            t
        )
        (
            t (proveri_element_p el (cdr lista))
        )
    )
)

;; GLAVNA FJA ZA PROVERU
;; agrument: cvorovi - npr svi potezi koje je odigrao 'X u formatu : (setq cvorovi '((5 2) (5 3) (6 2) (7 5) (8 4) (8 5))) ;; nije
(defun proveri_prsten_cvorovi (cvorovi)
    (let*
        (
            (br_min_cvorova 6)
            (sve_g_l_ivice3 (nadji_sve_gornje_leve_ivice cvorovi cvorovi))
            (sve_d_d_ivice3 (nadji_sve_donje_desne_ivice cvorovi cvorovi))

            (sve_g_d_ivice3 (nadji_sve_gornje_desne_ivice cvorovi cvorovi))
            (sve_d_l_ivice3 (nadji_sve_donje_leve_ivice cvorovi cvorovi))
        )
        (if (< (length cvorovi) 6)
            '()
            (or
                (proveri_prsten_za_sve_gl_dd_ivice sve_g_l_ivice3 sve_d_d_ivice3 cvorovi) 
                (proveri_prsten_za_sve_gd_dl_ivice sve_g_d_ivice3 sve_d_l_ivice3 cvorovi)
            )
        )
    )
)
(defun proveri_prsten_za_sve_gd_dl_ivice (sve_g_ivice3 sve_d_ivice3 cvorovi)
    (cond
        (
            (null sve_g_ivice3)
            '()
        )
        (
            (proveri_prsten_za_dl_ivice (car sve_g_ivice3) sve_d_ivice3 cvorovi)
            t
        )
        (
            t
            (proveri_prsten_za_sve_gd_dl_ivice (cdr sve_g_ivice3) sve_d_ivice3 cvorovi)
        )
    )
)
(defun proveri_prsten_za_sve_gl_dd_ivice (sve_g_ivice3 sve_d_ivice3 cvorovi)
    (cond
        (
            (null sve_g_ivice3)
            '()
        )
        (
            (proveri_prsten_za_dd_ivice (car sve_g_ivice3) sve_d_ivice3 cvorovi)
            t
        )
        (
            t
            (proveri_prsten_za_sve_gl_dd_ivice (cdr sve_g_ivice3) sve_d_ivice3 cvorovi)
        )
    )
)
(defun proveri_prsten_za_dd_ivice (gl_ivica3 sve_dd_ivice3 cvorovi)
    (cond
        (
            (null sve_dd_ivice3)
            '()
        )
        (
            t
            (let*
                (
                    (dd_ivica3 (car sve_dd_ivice3))
                    (bool1 (proveri_rastojanje_ivica nil (car dd_ivica3) (car gl_ivica3) nil )) ;; za cvor iz ivica
                    (bool2 (proveri_rastojanje_ivica1 nil (cadr dd_ivica3) (cadr gl_ivica3) nil )) ;; za ivica1 
                    (bool3 (proveri_rastojanje_ivica2 nil (caddr dd_ivica3) (caddr gl_ivica3) nil )) ;; za ivica2
                
                    (put (nadji_put_izmedju_i2_i1 gl_ivica3 dd_ivica3 cvorovi))
                    (put1 (nadji_put_izmedju_i1_i2 gl_ivica3 dd_ivica3 cvorovi)) ;;disj
                    (presek (nadji_presek put1 put))
                )                  
                (cond
                    (
                        (and bool1 bool2 bool3)
                        (if
                            (and (not (null put)) (not (null put1))) ;;disj
                            (if (null presek) ;;disj
                                t 
                                (if (proveri_prsten_za_dd_ivice gl_ivica3 sve_dd_ivice3 (proveri_obradjene_p cvorovi presek))
                                    t
                                    (proveri_prsten_za_dd_ivice gl_ivica3 (cdr sve_dd_ivice3) cvorovi)                                
                                )
                            )
                            
                            (proveri_prsten_za_dd_ivice gl_ivica3 (cdr sve_dd_ivice3) cvorovi)
                        )
                        
                    )
                    (
                        t
                        (proveri_prsten_za_dd_ivice gl_ivica3 (cdr sve_dd_ivice3) cvorovi)
                    )
                )
            )
        )
    )
)
;; GORNJDA DESNA I DONJA LEVA
(defun proveri_prsten_za_dl_ivice (gd_ivica3 sve_dl_ivice3 cvorovi)
    (cond
        (
            (null sve_dl_ivice3)
            '()
        )
        (
            t
            (let*
                (
                    (dl_ivica3 (car sve_dl_ivice3))
                    (bool1 (proveri_rastojanje_ivica (car dl_ivica3) nil nil (car gd_ivica3))) ;; za cvor iz ivica
                    (bool2 (proveri_rastojanje_ivica1 (cadr dl_ivica3) nil nil (cadr gd_ivica3))) ;; za ivica1 
                    (bool3 (proveri_rastojanje_ivica2 (caddr dl_ivica3) nil nil (caddr gd_ivica3))) ;; za ivica2
                    (put (nadji_put_izmedju_i2_i1 gd_ivica3 dl_ivica3 cvorovi))
                    (put1 (nadji_put_izmedju_i1_i2 gd_ivica3 dl_ivica3 cvorovi))
                    (presek (nadji_presek put1 put))
                )                  
                (cond
                    (
                        (and bool1 bool2 bool3)
                        (if
                            (and (not (null put)) (not (null put1)))
                            (if (null presek) 
                                t
                                (if 
                                    (proveri_prsten_za_dl_ivice gd_ivica3 sve_dl_ivice3 (proveri_obradjene_p cvorovi presek))
                                    t
                                    (proveri_prsten_za_dl_ivice gd_ivica3 (cdr sve_dl_ivice3) cvorovi)
                                )
                                
                            )
                            (proveri_prsten_za_dl_ivice gd_ivica3 (cdr sve_dl_ivice3) cvorovi)
                        )
                        
                    )
                    (
                        t
                        (proveri_prsten_za_dl_ivice gd_ivica3 (cdr sve_dl_ivice3) cvorovi)
                    )
                )
            )
        )
    )
)

(defun proveri_rastojanje_ivica (idl idd igl igd)
    (cond
        (
            (and (not (null igl )) (not (null idd ))
                (>= (abs (- (cadr igl) (cadr idd))) 2 ) 
                (>= (abs (- (car igl) (car idd))) 2 )
            )
            t
        )
        (
            (and (not (null igd )) (not (null idl ))
                (>= (abs (- (cadr igd) (cadr idl))) 2 ) 
                (>= (abs (- (car igd) (car idl))) 2 )
            )
            t 
        )
        (
            t
            '()
        )
    )
)
(defun proveri_rastojanje_ivica1 (idl idd igl igd)
    (cond
        (
            (and (not (null igl )) (not (null idd )) (>= (- (cadr idd) (cadr igl)) 2 ) )
            t
        )
        (
            (and (not (null igd )) (not (null idl )) (>= (- (cadr igd) (cadr idl)) 2 ))
            t
        )
        (
            t
            '()
        )

    )
)
(defun proveri_rastojanje_ivica2 (idl idd igl igd)
    (cond
        (
            (and (not (null igl )) (not (null idd )) 
                (>= (- (car idd) (car igl)) 2 ) )
            t 
        )
        (
            (and (not (null igd )) (not (null idl ))
                (>= (- (car idl) (car igd)) 2 ))
            t 
        )
        (
            t
            '()
        )
    )
)

(defun nadji_sve_gornje_desne_ivice (lista_o lista_c) ;; moze da se optimizuje uz sort i dodaj...
    (cond
        (
            (or (equal nil lista_o)(null lista_o))
            '() 
        )
        (t
            (let*    
                (
                    (ivica_cela (nadji_gornju_desnu_ivicu (car lista_o) lista_c) )
                )
                (cond
                    (
                        (null ivica_cela)
                        (nadji_sve_gornje_desne_ivice (cdr lista_o) lista_c )
                    )
                    (
                        t
                        (cons ivica_cela (nadji_sve_gornje_desne_ivice (cdr lista_o) lista_c ) )
                    )
                )
             )
        )
    )
)
(defun nadji_sve_donje_desne_ivice (lista_o lista_c) ;; moze da se optimizuje uz sort i dodaj...
    (cond
        (
            (or (equal nil lista_o)(null lista_o))
            '() 
        )
        (t
            (let*    
                (
                    (ivica_cela (nadji_donju_desnu_ivicu (car lista_o) lista_c) )
                )
                (cond
                    (
                        (null ivica_cela)
                        (nadji_sve_donje_desne_ivice (cdr lista_o) lista_c )
                    )
                    (
                        t
                        (cons ivica_cela (nadji_sve_donje_desne_ivice (cdr lista_o) lista_c ) )
                    )
                )
             )
        )
    )
)
(defun nadji_sve_donje_leve_ivice (lista_o lista_c) ;; moze da se optimizuje uz sort i dodaj...
    (cond
        (
            (or (equal nil lista_o)(null lista_o))
            '() 
        )
        (t
            (let*    
                (
                    (ivica_cela (nadji_donju_levu_ivicu (car lista_o) lista_c) )
                )
                (cond
                    (
                        (null ivica_cela)
                        (nadji_sve_donje_leve_ivice (cdr lista_o) lista_c )
                    )
                    (
                        t
                        (cons ivica_cela (nadji_sve_donje_leve_ivice (cdr lista_o) lista_c ) )
                    )
                )
             )
        )
    )
)
(defun nadji_sve_gornje_leve_ivice (lista_o lista_c) ;; moze da se optimizuje uz sort i dodaj...
    (cond
        (
            (or (equal nil lista_o)(null lista_o))
            '() 
        )
        (t
            (let*    
                (
                    (ivica_cela (nadji_gornju_levu_ivicu (car lista_o) lista_c) )
                )
                (cond
                    (
                        (null ivica_cela)
                        (nadji_sve_gornje_leve_ivice (cdr lista_o) lista_c )
                    )
                    (
                        t
                        (cons ivica_cela (nadji_sve_gornje_leve_ivice (cdr lista_o) lista_c ) )
                    )
                )
             )
        )
    )
)

(defun nadji_gornju_desnu_ivicu (cvor lista_cvorova) ;; mozda ce da vracaju bas bas ivicu tj cvor
(cond     
    (
        (null cvor)
        '()
    )
    (t
        (let*
            (
                ;; (cvor (car cvorovi))
                (ivica2 (cons (car cvor) (list (1- (cadr cvor))) ) ) 
                (ivica1 (cons (1+ (car cvor)) (list (cadr cvor)) ) ) 
            )
            (cond

                (
                    (postoje_li_ivice ivica1 ivica2 lista_cvorova 0)
                    (cons cvor (cons ivica1 (list ivica2)))
                )
                (
                    t
                    '()
                )
            )
        )
    )
)
)
(defun nadji_gornju_levu_ivicu (cvor lista_cvorova) 
(cond     
    (
        (null cvor)
        '()
    )
    (t
        (let*
            (
                ;; (cvor (car cvorovi))
                (ivica2 (cons (car cvor) (list (1+ (cadr cvor))) ) ) 
                (ivica1 (cons (1+ (car cvor)) (list (cadr cvor)) ) ) 
            )
            (cond

                (
                    (and (postoje_li_ivice ivica1 ivica2 lista_cvorova 0))
                    (cons cvor (cons ivica1 (list ivica2)))
                )
                (
                    t
                    '()
                )
            )
        )
    )
)
)


(defun nadji_donju_desnu_ivicu (cvor lista_cvorova) ;; vraca (cvor ivica1 ivica2)
(cond     
    (
        (null cvor)
        '()
    )
    (t
        (let*
            (
                (ivica1 (cons (1- (car cvor)) (list (cadr cvor)) ) ) 
                (ivica2 (cons (car cvor) (list (1- (cadr cvor))) ) ) 
            )
            (cond

                (
                    (and (postoje_li_ivice ivica1 ivica2 lista_cvorova 0))
                    (cons cvor (cons ivica1 (list ivica2)))
                )
                (
                    t
                    '()
                )
            )
        )
    )
)
)
(defun nadji_donju_levu_ivicu (cvor lista_cvorova)
(cond     
    (
        (null cvor)
        '()
    )
    (t
        (let*
            (
                (ivica1 (cons (1- (car cvor)) (list (cadr cvor))) ) 
                (ivica2 (cons (car cvor) (list (1+ (cadr cvor)))) ) 
            )
            (cond

                (
                    (and (postoje_li_ivice ivica1 ivica2 lista_cvorova 0))
                    (cons cvor (cons ivica1 (list ivica2)))
                )
                (
                    t
                    '()
                )
            )
        )
    )
)
)

(defun postoje_li_ivice(ivica1 ivica2 cvorovi flag)
    (cond
        (
            (= 2 flag)
            t
        )
        (
            (null cvorovi)
            '()
        )
        (
            (equal ivica1 (car cvorovi)) 
            (postoje_li_ivice ivica1 ivica2 (cdr cvorovi) (1+ flag))
        )
        (
            (equal ivica2 (car cvorovi)) 
            (postoje_li_ivice ivica1 ivica2 (cdr cvorovi) (1+ flag))
        )
        (
            t
            (postoje_li_ivice ivica1 ivica2 (cdr cvorovi) flag)
        )
    )
)

;; PROVERA PRSTEN EEEND ~~~~~
(defun vrati_pomeraj_slova (slovo konacnalista)
    (cond 
        (
            (null konacnalista)
            '()
        )
        (
            (equal (caar konacnalista) slovo)
            (car (cdr (cdr (car konacnalista))))
        )
        (
            t
            (vrati_pomeraj_slova slovo (cdr konacnalista))

        )
    )
)
(defun generisi_slovca(n lista) ;;generise gore opisanu listu oblika '((A 0) (B 1)..) koja ce imati onoliko elemenata koliko ce biti vrsta na tabli u zavisnosti od velicine table
    (cond
     ((= n 1 ) (cons (car lista) '()))
     (t  (cons (car lista) (generisi_slovca (1- n) (cdr lista))))
    )
)
(defun generisi_pomeraje(n listazaigru) ;;generise gore opisanu listu oblika '((A 0 5) (B 1 4)..) gde je poslednji element svake podliste pomeraj koji nam je potreban za validno ispisivanje i igranje poteza
    (cond
        (
            (null listazaigru)
            '()
        )
        (
           (> n 0)
           (cons (append (car listazaigru) (list (1- n))) (generisi_pomeraje(1- n) (cdr listazaigru)))
        )
        (
            t
            (cons (append (car listazaigru) (list 0)) (generisi_pomeraje(1- n) (cdr listazaigru)))
        )
    )
)
(defun generisi_nedozvoljene (lista pocetak kraj) ;;generise listu nedozvoljenih poteza oblika '((A 0 5) (B 0 6)..) gde su poslednja dva elementa svake podliste redom minimalna odnosno maksimalna vrednost kolone validnog poteza za odgovarajuce slovo
    (cond
            (
                (null lista)
                '()
            )
            (
                (< kraj (- (* 2 velicina_table) 2))
                (cons (cons (caar lista) (append (list pocetak) (list kraj))) (generisi_nedozvoljene (cdr lista) pocetak (1+ kraj)))
            )
            (
                t
                (cons (cons (caar lista) (append (list pocetak) (list kraj))) (generisi_nedozvoljene (cdr lista) (1+ pocetak)  kraj))

            )

    )
)
(defun generisi_vrstu_stanja(n i pomeraj pom) ;;pomocna funkcija koja se zove iz funkcije generisi_stanje gde je n velcicina table,i uvek pocinje od 0 i sluzi nam za proveru
                                              ;; da li smo izgenerisali celu vrstu stanja,pomeraj je trenutni pomeraj(broj praznih polja sa leve strane) za zadatu vrstu
                                              ;;a pom je broj validnih pozicija za igranje za zadatu vrstu
   (setq nn (- (* 3 n ) 1))
    (cond
        (
            (= i (1- nn))
            '()
        )
        (
            (and (< i (+ pom pomeraj)) (>= i pomeraj))
            (cons (append (list i) (list 0)) (generisi_vrstu_stanja n (1+ i ) pomeraj pom))
        )
        (
            t
            (cons (append (list i) (list -1)) (generisi_vrstu_stanja n (1+ i ) pomeraj pom))
        )
    )
)
(defun generisi_stanje(n j pomeraj pom) ;; funkcija za generisanje pocetnog stanja oblika datog u dokumentu,gde je n velicina table,j pomocna promenljiva koja pocinje od 0,
                                        ;; i proverava da li smo dosli do kraja rekurzije(izgenerisali celo stanje)
                                        ;; ,pomeraj odredjuje pomeraj(broj praznih polja levo) za vrstu(raste do polovine table pa se smanjuje,pocinje od (1- velicina_table),
                                        ;; i pom je pomocna promenljiva koju postavljamo na velicinu table inicijalno i odredjuje nam broj validnih mesta za igru za zadatu vrstu,
                                        ;; povecavamo je za gornji,odnosno smanjujemo za donji deo tabela,radi tacne inicijalizacije stanja
    (setq mm (1+ (-(* 2 n) 1))) ;;broj odgovarajucih kolona
    (cond
       (
           (= j (1- mm)) ;;kraj rekurzije,vracamo praznu listu
           '()
       )
        (
            (>= j (- (floor mm 2) 1)) ;;druga polovina table,za nju se pomeraj (odnosno prazna polja sa leve stranje matrice) povecavaju,
                                      ;;a pom koji odredjuje broj validnih polja za igru za zadatu vrstu smanjuje
            (cons (cons j (generisi_vrstu_stanja n 0 pomeraj pom)) (generisi_stanje n (1+ j) (1+ pomeraj) (1- pom)))
        )
        (
            t                               ;;prva polovina table,za nju se pomeraj(odnosno prazna polja sa leve stranje matrice) smanjuje,
                                            ;;a pom koji odredjuje broj validnih polja za igru za zadatu vrstu povecava
            (cons (cons j (generisi_vrstu_stanja n 0 pomeraj pom)) (generisi_stanje n (1+ j) (1- pomeraj) (1+ pom) ))
        )
)
)


(defun ko_igra_prvi() ;;korisnik bira da li zeli da igra prvi ili ne,i u zavisnosti od toga se vraca odgovarjuca lista te se kao sto je gore opisano postavljaju
                      ;;odgovarajuci simboli simbol_covek i simbol_masina kao sto je gore opisano
    (print "Koji igrac igra prvi? (1/2)")
    (cond
        (
            (equal (read) 1)
            '(X O)
        )
        (
            t
            '(O X)
        )

    )

)
(defun biraj_trazenje() 

    (print "Da li zelite da se trazenje obavlja algoritmom minmax ili alphabeta? (1/2)")
    (cond
        (
            (equal (read) 1)
            0
        )
        (
            t
            1
        )

    )

)
(defun prikazi_celu_tablu() ;;celoukupni prikaz trenutno stanja table za igru

    (prikazi_brojeve_iznad 0 velicina_table (izracunaj_prazna_br_iznad konacna_lista)) ;;pomocna funkcija za ispisivanje validnih brojeva kolona iznad same table za igru
    (prikazi_tablu stanje (1- (* 2 velicina_table)) konacna_lista velicina_table velicina_table) ;;funkcija koja stampa trenutno stanje same table za igranje

)
(defun prikazi_brojeve_iznad(n velicina_matrice br_prazna_polja) ;;funkcija koja prikazuje odgovarajuce brojeve kolone iznad table u zavisnosti od velicine matrice

    (cond

        (
            (> br_prazna_polja 0)
            (cons (format t "  ") (prikazi_brojeve_iznad n velicina_matrice (1- br_prazna_polja)))
        )
        (
            (< n velicina_matrice)
            (cons (format t "  ~a  "n)(prikazi_brojeve_iznad (1+ n)velicina_matrice br_prazna_polja))
        )
        (t
        (format t "~%")
        )
    )
)
(defun izracunaj_prazna_br_iznad(konacna_lista) ;;pomocna funkcija koja racuna broj blanko znaka za ispis odgovarajucih brojeva kolone iznad table
    (+ (caddar konacna_lista) 1)
)
(defun prikazi_tablu(stanje n lista pom fiksnon) ;;funkcija za prikaz trenutnog stanja table,paremetri su samo stanje,n je broj vrsta,a pom i fiksnon pomocne promenljive koje pocinju od velicine_table
    (cond
        (
            (equal n 0)
            '()
        )
        (
            t
           (cons (format t " ~a" (broj_u_slovo(caar stanje) lista)) (cons (prikazi_vrstu (cdr (car stanje)) pom fiksnon) (prikazi_tablu (cdr stanje) (1- n) lista (1+ pom) fiksnon)))
        )

    )
)
(defun broj_u_slovo(broj lista) ;;prevodi broj vrste u slovo odredjeno tim brojem u zavisnosti od gore generisane liste konacna_lista
    (cond
        (
            (null lista)
            '()
        )
        (
            (equal (cadar lista) broj)
            (caar lista)
        )
        (
            t
            (broj_u_slovo broj (cdr lista))
        )
    )
)
(defun prikazi_vrstu(vrsta pom fiksnon) ;;pomocna funkcija za prikazivanje svake pojedinacne vrste,zove se iz prikazi_tablu za svaku vrstu i u zavisnosti od toga sta je na
                                        ;;mestu koje se trenutno obradjuje u matrici stampa '_' ukoliko je u matrici 0,simbole X ili O ukoliko su oni na datom mestu u matrici
                                        ;;dok ukoliko je u matrici -1 stampa blanko znake,te stampa odgovarjuce brojeve kolona sa desne strane table uz odgovarajucu proveru
    (cond
        (
            (null  vrsta)
            (format t "~%~%")
        )
        (
            (and (or (equal (cadar vrsta) 0) (equal (cadar vrsta) 'X) (equal (cadar vrsta) 'O)) (equal (cadr (car (cdr vrsta))) -1) (<= pom (- (* 2 fiksnon ) 2)))
            (if (equal (cadar vrsta) 0) (cons (cons (format t "  _  " ) (format t " ~a" pom)) (prikazi_vrstu (cdr vrsta) pom fiksnon)) (cons (cons (format t "  ~a  " (cadar vrsta)) (format t "  ~a  " pom)) (prikazi_vrstu (cdr vrsta) pom fiksnon))  )

        )
        (
            (equal (car (cdr (car vrsta))) -1)
            (cons (format t "  ") (prikazi_vrstu (cdr vrsta) pom fiksnon))
        )
        (
            (equal (car (cdr (car vrsta))) 0)
            (cons (format t "  _  ") (prikazi_vrstu (cdr vrsta) pom fiksnon))

        )
        (
            t
            (cons (format t "  ~a  " (car (cdr (car vrsta)))) (prikazi_vrstu (cdr vrsta) pom fiksnon))
        )
    )

)



(defun proveri_infere()
    (or 
        (infer '(AND (Pobednik 'X) (!viljuska)))
        (infer '(AND (Pobednik 'X) (!most) ))
        (infer '(AND (Pobednik 'X) (!prsten) ))
        (infer '(AND (Pobednik 'O) (!viljuska)))
        (infer '(AND (Pobednik 'O)(!most) ))
        (infer '(AND (Pobednik 'O) (!prsten) ))   
    )
)

(defun !viljuska() 
    fork
)
(defun !most()
    most
)
(defun !prsten()
    prsten
)

(defparameter *JULIJAN-RULES* 
    '(
	    (if (NaPotezu ?igrac) and (KrajIgre ?stanje) then (Pobednik ?igrac))
    )
)    
(defparameter *JULIJAN-FACTS* 
    '(
	    (KrajIgre 'Viljuska)
	    (KrajIgre 'Most)
	    (KrajIgre 'Prsten)
        (NaPotezu 'X)
        (NaPotezu 'O)
        (Pobednik 'X)
        (Pobednik 'O)
    )
)
;;(prepare-knowledge *JULIJAN-RULES* *JULIJAN-FACTS* 10)

;;nova pravila
(defparameter *JULIJANV2-RULES* 
    '(
	    (if (X ?brojsuseda) then (SusedX ?brojsuseda))
        (if (O ?brojsuseda) then (SusedO ?brojsuseda))
        (if (and (PobednikX ?pobeda) (!eq ?pobeda t)) then (PobedioX))
        (if (and (PobednikO ?pobeda) (!eq ?pobeda t)) then (PobedioO))
    )
)
(defun !eq (a b)
  (equal a b)
)  
;;formiranje liste cinjenica
(defun formiraj_listu_cinjenica (stanje)
    (append (formiraj_listu_suseda (formiraj_listu_poteza stanje) stanje) (list (list 'PobednikX (proveri_kraj stanje 'X))) (list (list 'PobednikO (proveri_kraj stanje 'O))))
)
;;formira cinjenicu tipa (X 1) gde je drugi parametar broj suseda datog cvora x
(defun formiraj_listu_suseda (lista stanje)
    (cond 
        
            (
                (null lista)
                '()
            )
            (t 
                (cons (cons (caar lista) (list (length (nadji_susede (formiraj_potez (car (cdr (car lista))) (car (cdr (cdr (car lista))))) (caar lista) stanje))))   (formiraj_listu_suseda (cdr lista) stanje)  )
            )
       
    )
)
;;fomira listu svih odigranih poteza
(defun formiraj_listu_poteza(stanje)
    (cond 
        (
            (null stanje)
            '()
        )
        (
            t
            (append (spoji (caar stanje) (izdvoji_elemente (cdr (car stanje))) ) (formiraj_listu_poteza (cdr stanje)) )
        )
    )
)
;;pomocne funkcije koje se ne koriste,samo se koristi gornja formiraj listu suseda,nismo stigli da obrisemo kao ni stara rules i facts
(defun spoji(vrsta kolonasimbol)
    (cond 
        (
            (null kolonasimbol)
            '()
        )
        (t 
            (cons (cons (car (cdr (car kolonasimbol))) (cons vrsta  (list (caar kolonasimbol))) )   (spoji vrsta (cdr kolonasimbol)))
        )
    )
)
(defun izdvoji_elemente(vrsta)
    (cond 
        (
            (null vrsta)
            '()
        )
        (
            (or (equal (car (cdr (car vrsta))) -1) (equal (car (cdr (car vrsta))) 0))
            (izdvoji_elemente (cdr vrsta))

        )
        (t 
            (cons (car vrsta) (izdvoji_elemente (cdr vrsta)))
        )

    )
)


(defun igraj() ;;u zavisnosti od toga da li covek igra prvi ili ne,ulazi se u jednu od dve beskonacne petlje (odnosno loopa) za igranje,gde (unesi_potez) odgovara unosenju covekovog poteza i njegovom odigravanju,a (igra_kompjuter) analogno samo za masinu(trenutno masina igra random poteze)

    ;; (if (equal simbol_prvi_igrac 'X)
      
    ;;    (loop while (not (or fork most prsten) ) do (nastavi_igru simbol_prvi_igrac 1)  (if  (proveri_infere) (format t "Kraj igre!~%") (igra_kompjuter simbol_drugi_igrac)))

    ;;    (loop while (not (or fork most prsten)) do (igra_kompjuter simbol_drugi_igrac ) (if (proveri_infere) (format t "Kraj igre!~%") (nastavi_igru simbol_prvi_igrac 1)))
  

    ;; )
    
    (if (equal simbol_prvi_igrac 'X)
      
       (loop while (not (or fork most prsten) ) do (nastavi_igru simbol_prvi_igrac 1)  (if  (or fork most prsten) (format t "Kraj igre!~%") (nastavi_igru simbol_drugi_igrac 2)))

       (loop while (not (or fork most prsten)) do (nastavi_igru simbol_drugi_igrac 2) (if (or fork most prsten) (format t "Kraj igre!~%") (nastavi_igru simbol_prvi_igrac 1)))
  

    )
)



(defun nastavi_igru(simbol br) 
(unesi_potez simbol br)
(prikazi_celu_tablu)
(povecajfaktor) 
)
(defun unesi_potez(simbol rednibrojigraca) ;;unosenje poteza od strane korisnika
    (format t "Unesi potez u odgovarajucem formatu(na potezu je Igrac ~a ): " rednibrojigraca)
    (setq x (read))
    (setq y (read))
    (if (proveri_potez x y lista_nedozvoljenih) (prevedi_potez x y simbol rednibrojigraca stanje 0) (unesi_potez simbol rednibrojigraca) ) ;;vrsi se provera poteza,ukoliko je potez validan onda se prevodi i odigrava,a ukoliko nije stampa se odgovarajuca poruka
    (if (proveri_viljuska (list (list (slovo_u_broj x konacna_lista) (+ y (nadji_pomeraj x konacna_lista)))) simbol stanje) (setq fork 'T) (setq fork '())) 
    (if (most simbol lista_temena stanje) (setq most 'T) (setq most '()))
    (if (proveri_prsten_cvorovi (vrati_sve simbol stanje) ) (setq prsten 'T) (setq prsten '()))
 
    ;;(print pomocnacetridva)
)

(defun proveri_potez (x y listanedoz) ;;proveravamo samo da li je uneti potez u granicama table za odgovarajucu unetu kombinaciju vrsta kolona,na primer H 4
                                      ;;uz pomoc gore generisane liste nedozvoljenih poteza
    (cond
        (
            (null listanedoz)
            '()
        )
        (
            (equal (caar listanedoz) x)
            (if  (and (>= y (car (cdr (car listanedoz)))) (<= y (caddar listanedoz))) T '())
        )
        (
            t
            (proveri_potez x y (cdr listanedoz))
        )
    )
)
(defun prevedi_potez (slovce broj simbol trenutnoigra pomstanje flag) ;;potez unet od strane coveka se prevodi u odgovarjuce vrednosti radi njegovog smestanja u stanje
                                                        ;; i kasnijeg ispisa na tablu

    (setq vrsta (slovo_u_broj slovce konacna_lista))
    (setq kolona (+ broj (nadji_pomeraj slovce konacna_lista)))
    (cond
        (
            (= flag 1)
            (postavi simbol vrsta kolona pomstanje)
        )

       (
           (and (equal stanje (postavi simbol vrsta kolona pomstanje)) (equal trenutnoigra 1)) ;;ako se stanje nije promenilo,sto znaci da je potez u granicama table ,
                                                                                            ;;ali je to polje zauzeto,a trenutno igra covek,onda on treba ponovo da unese(odigra)
                                                                                            ;;potez
           (unesi_potez simbol_prvi_igrac 1)
       )
       (
           (and (equal stanje (postavi simbol vrsta kolona pomstanje)) (equal trenutnoigra 2)) ;;ako se stanje nije promenilo,sto znaci da je potez u granicama table ,
                                                                                            ;;ali je to polje zauzeto,a trenutno igra masina,onda opet treba da odigra masina
           (unesi_potez simbol_drugi_igrac 2)
       )
       (
           t
           (setq stanje (postavi simbol vrsta kolona pomstanje))          ;;stanje se promenilo i samo setujemo stanje na novo stanje
       )

    )
)
(defun slovo_u_broj(slovo konacnalista) ;;vrsi prevodjenje slova u odgovarajuci broj vrste koristeci gore generisanu listu
    (cond
        (
            (null konacnalista)
            '()
        )
        (
           (equal (car (car konacnalista)) slovo)
           (car (cdr (car konacnalista)))
        )
        (
            t
            (slovo_u_broj slovo (cdr konacnalista))
        )
    )
)
(defun nadji_pomeraj(slovo listapomeraja) ;;trazi i vraca pomeraj za odgovarujuce slovo iz gore generisane liste
    (cond
        (
            (null listapomeraja)
            '()
        )
        (
            (equal (car (car listapomeraja)) slovo)
            (car (cdr (cdr (car listapomeraja))))
        )
        (
            t
            (nadji_pomeraj slovo (cdr listapomeraja))
        )

    )
)
(defun postavi (el r c mat) ;;postavlja element el,koji se nalazi u vrsti r,i koloni c,u datu matricu mat(matrica je u ovom slucaju nase stanje)
    (cond
        (
            (= 0 r)
            (cons (pomocna el c (car mat)) (cdr mat)) ;;kada je r=0 dosli smo do zadate vrste i zovemo pomocnu funkciju da bismo dosli do zadate kolone
        )
        (
            t
            (cons (car mat) (postavi el (1- r) c (cdr mat))) ;;preskacemo vrstu posto ona nije ta koju trazimo
        )
    )
)

(defun pomocna (el c red)
    (cond
        (
            (= -1 c)  ;;dosli smo do kolone koju trazimo,ubacujemo element na odgovarajuce mesto
            (if (equal (cadar red) 0) (cons (append (list (car (car red))) (list el)) (cdr red)) red )
        )
        (
            t
            (cons (car red) (pomocna el (1- c) (cdr red))) ;;preskacemo kolonu posto ona nije ta koju trazimo
        )
    )
)
(defun generisi_sledece_stanje_v2(potez simboligracanapotezu pstanje) ;;generise sledece moguce stanje bez promene tekuceg stanja igre,odnosno igra se potez na pstanju
    (prevedi_potez (car potez) (car (cdr potez)) simboligracanapotezu -1 pstanje 1)
)
(defun sva_sledeca_stanja(listapraznih simboligracanapotezu pstanje)
    (cond 
        (
            (null listapraznih)
            '()
        )
        (
            t 
            (cons (generisi_sledece_stanje_v2 (car listapraznih) simboligracanapotezu pstanje) (sva_sledeca_stanja (cdr listapraznih) simboligracanapotezu pstanje))
        )
    
    )
)
(defun vrati_listu_pozicija_praznih(pomstanje)
(cond
    (
        (null (cdr pomstanje))
        (append (kombinuj (caar pomstanje) (vrati_listu_pozicija_praznih_vrsta (cdr (car pomstanje)))) '() )
    )
    (t
        
        (append (kombinuj (caar pomstanje) (vrati_listu_pozicija_praznih_vrsta (cdr (car pomstanje)))) (vrati_listu_pozicija_praznih (cdr pomstanje))) 
    )
)
)
(defun kombinuj (slovo vrsta)
    (cond 
        (
            (null (cdr vrsta))
            '()
        )
        (t
            (cons (cons (broj_u_slovo slovo konacna_lista) (list  (- (car vrsta) (nadji_pomeraj (broj_u_slovo slovo konacna_lista) konacna_lista)))) (kombinuj slovo (cdr vrsta))   )
        )

    
    )
)
(defun vrati_listu_pozicija_praznih_vrsta(lista)

    ;;(print lista)
    (cond 
        (
            (null (cdr lista))
            (cons (caar lista)'()) 
        )
        (
            (not (equal  (car (cdr (car lista)))  0))
            (vrati_listu_pozicija_praznih_vrsta (cdr lista))
        )
        (t
           
            
            (cons  (caar lista) (vrati_listu_pozicija_praznih_vrsta (cdr lista)))
        
        )
    )

)
(defun nadji_temena( stanje) 
(append  (append

 (cons (cons  (car (car stanje)) (cdr (cdr (car konacna_lista)))) (list (cons (car (car stanje)) (list (- (+ (car (cdr (cdr (car konacna_lista))))  velicina_table)  1)) )))  
 
 (cons (cons  (car (nth (1- velicina_table) stanje)) (cdr (cdr (nth (1- velicina_table) konacna_lista)))) (list (cons (car (nth (1- velicina_table) stanje)) (list (- (+ (car (cdr (cdr (nth (1- velicina_table) konacna_lista))))  (* 2 velicina_table))  2)) ))) 

)

(cons (cons  (car (nth (- (* velicina_table 2) 2) stanje)) (cdr (cdr (car konacna_lista))))  (list (cons (car (nth (- (* velicina_table 2) 2) stanje)) (list (- (+ (car (cdr (cdr (car konacna_lista))))  velicina_table)  1)) )))



))
(defun generisi_f(lista pocetni flag)  
    (cond 
        (
            (null lista)
            '()
        )
        (
            (= flag 1)
           (cons (cons (car (cdr (car lista))) (list pocetni)) (generisi_f (cdr lista) (1+ pocetni) 1)) 
        )
        (
            (> pocetni 0)
            (cons (cons (car (cdr (car lista))) (list pocetni))  (generisi_f (cdr lista) (1- pocetni) 0) ) 
        )
        (t
            (cons (cons (car (cdr (car lista))) (list pocetni))  (generisi_f (cdr lista) (1+ pocetni) 1)) 
        )
    
    )
)
;;aleksa
(defun vrati_prvi (broj lista)
    (cond 
        (
            (null lista)
            '()
        )
        (
            (equal (caar lista) broj)
            (car (cdr (car lista)))
        )
        (
            t
            (vrati_prvi broj (cdr lista))
        )
    )
)
;;(defun nadji_pomeraj(broj listapomeraja) ;;trazi i vraca pomeraj za odgovarujuce slovo iz gore generisane liste
 ;;   (cond
  ;;      (
          ;;  (null listapomeraja)
         ;;   '()
        ;;)
        ;;(
           ;; (equal (car (cdr (car listapomeraja))) broj)
         ;;   (car (cdr (cdr (car listapomeraja))))
       ;; )
     ;;   (
        ;;    t
      ;;      (nadji_pomeraj slovo (cdr listapomeraja))
    ;;    )

  ;;  )
;;)
(defun nadji_susede (cvor simbol stanje)
    (if 
        (and (>= (car cvor) 0) (>= (cadr cvor) 0) (< (car cvor) nn) (< (cadr cvor) mm)) 
        (nadji_potomke cvor -1 simbol stanje 3) 
        '()
    )
)


(defun nadji_potomke  (cvor pom simbol stanje tri)
    (cond
        (
            (> tri 0)
            (append 
                (nadji_potomke_vrsta cvor (+ (car cvor) pom) (- (cadr cvor) 1) simbol stanje 3) 
                (nadji_potomke cvor (1+ pom) simbol stanje (1- tri) )
            ) 
        )
    )
)
(defun nadji_potomke_vrsta (cvor i j simbol stanje tri)
    (setq pronadjenCvor (simbol_je_na_poziciji simbol i j stanje))
    (cond
        (
            (= tri 0)
            '()
        ) 
        (
            (and 
                (not (null pronadjenCvor)) (not (equal pronadjenCvor cvor)) (> tri 0)
                (>= i 0) (>= j 0) (< i nn) (< j mm)
            )
            (cons pronadjenCvor (nadji_potomke_vrsta cvor i (1+ j) simbol stanje (1- tri)))
        )
        (
            t
            (nadji_potomke_vrsta cvor i (1+ j) simbol stanje (1- tri))
        )
    )
)

(defun simbol_je_na_poziciji (simbol i j stanje)
    (if 
        (and (>= i 0) (>= j 0) (< i nn) (< j mm)) 
        (let*
            (
                (red (nth i stanje))
                (polje (nth (1+ j) red))
            )
            (cond  
                ( 
                    (equal simbol (cadr polje))
                    (cons i (list j))
                )
                (
                    t
                    '()
                )
            )
        ) 
        '() 
    )
)
(defun nadji_put_d (l cvorovi simbol) ;; nalazi cvorove koji se nalaze u disjunktnom putu
    (cond 
        ((null l) cvorovi)
        (t
            (let*
                (
                  (cvorovi1 (append cvorovi (list (car l))))
                  (potomci1 (dodaj_potomke_bfs (car l) (append (cdr l) cvorovi1) simbol))
                  (l1 (append (cdr l) potomci1))
                )
                (nadji_put_d l1 cvorovi1 simbol)
            )
        )
    )
)
(defun nadji_put_bfs(l cilj cvorovi simbol stanje)
    (cond 
        (
            (null l) 
            '()    
            
        )
        (
            (equal (car l)  cilj) 
            (list (car l))
        )
        (
            t
            (let* 
                (
                    (cvorovi1 (append (list (car l)) cvorovi))
                    (potomci1 (dodaj_potomke_bfs (car l) (append (cdr l) cvorovi) simbol stanje))
                    (l1 (append (cdr l) potomci1))
                    (nadjeni-put (nadji_put_bfs l1 cilj cvorovi1 simbol stanje))
                )
                (cond 
                  (
                      (null nadjeni-put) '()
                  )
                  (
                      (not (proveri_element (car nadjeni-put) potomci1)) 
                      (cons (car l) nadjeni-put)
                  )
                  (:else nadjeni-put)
                )
        )
        )
    )
)

(defun dodaj_potomke_bfs(cvor cvorovi simbol stanje)
    (let*
        (
            (susedi (nadji_susede cvor simbol stanje))
           
        )
        (proveri_obradjene susedi cvorovi)
    )
)
(defun proveri_obradjene(lista1 lista2)
    (cond 
        (
            (null lista1)
            '()
        )
        (
            (proveri_element (car lista1) lista2)
            (cons (car lista1) (proveri_obradjene (cdr lista1) lista2))
        )
        (t
            (proveri_obradjene (cdr lista1) lista2)
        )

    )
)
(defun proveri_element (el lista)
    (cond 
        (
            (null lista)
            t
        )
        (
            (equal el (car lista))
            '()
        )
        (
            t
            (proveri_element el (cdr lista))
        )
    )
)


(defun vrati_stranice_table(pomstanje simbol)
    (cond
        (
            (null pomstanje)
            '()
        )
        (
           (or (equal (caar pomstanje) 0) (equal (caar pomstanje) (- (* 2 velicina_table) 2) ))
           (append (kombinuj_broj (caar pomstanje) (vrati_celu_stranu (cdr (car pomstanje)) simbol))  (vrati_stranice_table (cdr pomstanje) simbol)) 
        )
        (t
            (append (kombinuj_broj (caar pomstanje) (vrati_prvi_i_poslednji(cdr (car pomstanje)) simbol (vrati_prvi (caar pomstanje) moja_lista)))  (vrati_stranice_table (cdr pomstanje) simbol))
        )
    )
)
(defun kombinuj_broj (broj lista)
    (cond 
        (
            (null lista)
            '()
        )
        (t
            (cons (append (list broj) (list (car lista))) (kombinuj_broj broj (cdr lista)))
        )
    
    )
)
(defun vrati_celu_stranu(lista simbol)
    (cond 
        (
            (null lista)
            '()
        )
        (
            (equal (car (cdr (car lista)))  simbol)
            (cons (caar lista) (vrati_celu_stranu (cdr lista) simbol) )
        )
        (
            t
            (vrati_celu_stranu (cdr lista) simbol)
        )
    )
)
(defun vrati_prvi_i_poslednji(lista simbol ind)
    (cond 
        (
            (null lista)
            '()
        )
        (
            (or (equal ind (caar lista)) (and  (not (equal (cadar lista) -1))  (equal (cadar (cdr lista))  -1))) ;;ovde treba da preko ovog sto sam generisao sad dobijem vrednost umesto 0
            (if (equal (car (cdr (car lista))) simbol) (cons (caar lista) (vrati_prvi_i_poslednji (cdr lista) simbol  ind)) (vrati_prvi_i_poslednji (cdr lista) simbol ind))
        )
        (
            t
            (vrati_prvi_i_poslednji (cdr lista) simbol ind)
        )
    
    )
)
(defun vrati_gornju (lista)
    (cond
        (
            (null lista)
            '()
        )
        (
            (and (equal (caar lista) 0)  (>= (car (cdr (car lista))) velicina_table) (< (car (cdr (car lista))) (- (* 2 velicina_table ) 2)) )
            (cons (car lista) (vrati_gornju (cdr lista)))
        )
        (t 
             (vrati_gornju(cdr lista))  
        )
    )
)
(defun vrati_donju (lista)
       (cond
        ( 
            (null lista)
            '()
        )
        (
            (and (equal (caar lista) (- (* 2 velicina_table ) 2) )   (>= (car (cdr (car lista))) velicina_table) (< (car (cdr (car lista))) (- (* 2 velicina_table ) 2)) )  
            (cons (car lista) (vrati_donju (cdr lista)))
        )
        (t 
             (vrati_donju(cdr lista))  
        
        )
       )

)
(defun vrati_gore_levo(lista)
    (cond 
        (
            (null lista)
            '()
        )
        (
            (and (< (caar lista) (- velicina_table 1)) (> (caar lista) 0) (< (car (cdr (car lista))) velicina_table ))
            (cons (car lista) (vrati_gore_levo (cdr lista)))
        )
        (t
            (vrati_gore_levo(cdr lista))
        )
    )
)
(defun vrati_gore_desno (lista)
    (cond 
        (
            (null lista)
            '()
        )
        (
            (and (<= (caar lista) (- velicina_table 2)) (> (caar lista) 0) (equal (car (cdr (car lista))) (- (* 2 velicina_table) 2)) )  
            (cons (car lista) (vrati_gore_desno(cdr lista)))
        )
        (t 
            (vrati_gore_desno (cdr lista))
        )
    
    )
)
(defun vrati_dole_levo(lista)
    (cond 
        (
            (null lista)
            '()
        )
        (
            (and (> (caar lista) (- velicina_table 1)) (< (caar lista) (- (* 2 velicina_table) 2)) (< (car (cdr (car lista))) velicina_table ))
            (cons (car lista) (vrati_dole_levo (cdr lista)))
        )
        (t
            (vrati_dole_levo(cdr lista))
        )
    )

)
(defun vrati_dole_desno(lista)
     (cond 
        (
            (null lista)
            '()
        )
        (
            (and (>= (caar lista) velicina_table) (< (caar lista)  (- (* 2 velicina_table) 2)) (equal (car (cdr (car lista))) (- (* 2 velicina_table) 2)) )  
            (cons (car lista) (vrati_dole_desno(cdr lista)))
        )
        (t 
            (vrati_dole_desno (cdr lista))
        )
    
    )

)

(defun vrati_sve(simbol stanje)
    (cond 
        (
            (null stanje)
            '()
        )
        (t 
            (let* 
                (
                    (lista (vrati_sve_vrsta simbol (car stanje)))
                )
                
                    (if (null lista) (vrati_sve simbol (cdr stanje)) (append lista (vrati_sve simbol (cdr stanje))))    
                
            
            )
        )
    
    )
)
(defun vrati_sve_vrsta (simbol lista)
    (cond 
        ( 
            (= (length lista) 1)
            '()
        )
        (t 
            (if (equal (car (cdr (car (cdr lista))))  simbol) (cons (cons (car lista) (list (car (car (cdr lista)))))  (vrati_sve_vrsta simbol (cons (car lista) (cdr (cdr lista)))))  (vrati_sve_vrsta simbol (cons (car lista) (cdr (cdr lista))))) 
        )
    
    )

)
(defun proveri_viljuska_stanje(stanje simbol)
 
    (let* 
        (
            (lista (vrati_sve simbol stanje))
        )
        (proveri_viljuska_lista simbol lista stanje)

    )

)
(defun proveri_viljuska_lista(simbol lista stanje)
    (cond 
        (
            (null lista)
            '()
        )
        (t 
            (or (proveri_viljuska (list (car lista)) simbol stanje) (proveri_viljuska_lista simbol (cdr lista ) stanje))
        )
    )

)
(defun proveri_viljuska(pozicija simbol stanje)

      (let*
            (
                (putevi__do_gore (list (nadji_puteve_do_stranice pozicija simbol  (vrati_gornju (vrati_stranice_table stanje 'X)) stanje)))
                (putevi_do_gore_levo (list (nadji_puteve_do_stranice pozicija simbol  (vrati_gore_levo (vrati_stranice_table stanje 'X)) stanje)))
                (putevi_do_gore_desno (list (nadji_puteve_do_stranice pozicija simbol  (vrati_gore_desno (vrati_stranice_table stanje 'X)) stanje)))
                (putevi_do_dole_levo (list (nadji_puteve_do_stranice pozicija simbol  (vrati_dole_levo (vrati_stranice_table stanje 'X)) stanje)))
                (putevi_do_dole_desno (list (nadji_puteve_do_stranice pozicija simbol  (vrati_dole_desno (vrati_stranice_table stanje 'X)) stanje)))
                (putevi_do_dole (list (nadji_puteve_do_stranice pozicija simbol  (vrati_donju (vrati_stranice_table stanje 'X)) stanje)))
                (putevi (append putevi__do_gore putevi_do_dole putevi_do_dole_desno putevi_do_dole_levo putevi_do_gore_desno putevi_do_gore_levo))
                
                
            )

             (if (>= (prebroj_puteve putevi) 3)  T '())
        ) 

)
(defun nadji_puteve_do_stranice (pozicija simbol lista stanje)

    (cond 
        (
            (null lista)
            '()
        )
        (
            t
            (append (nadji_put_bfs pozicija (car lista) '() simbol stanje) (nadji_puteve_do_stranice pozicija simbol (cdr lista) stanje))
        )
    )

)
(defun prebroj_puteve(putevi) 
    (cond 
        (
            (null putevi) 0
        )    
        (
            (not (null (car putevi)))
            (1+ (prebroj_puteve (cdr putevi)))
        )
        (
            t 
            (prebroj_puteve (cdr putevi))
        )
    )
)

(defun most(simbol_igra lista stanje)
(cond 
((null lista) '())
(t

(or (most_za_jedan_el (car lista) simbol_igra lista stanje) (most simbol_igra (cdr lista) stanje))

)
)
)

(defun most_za_jedan_el(el simbol l stanje) 
(cond
(
    (null l) 
    '()
)
(
    (and (not (equal el (car l))) (proveri_simbol_teme el stanje simbol))
    (if (> (length (nadji_put_bfs (list el) (car l) '() simbol stanje)) 0) 't  (most_za_jedan_el el simbol (cdr l) stanje))



)
(t
  (most_za_jedan_el el simbol (cdr l) stanje)

)


)
)
(defun proveri_simbol_teme (el stanje simbol)
    (cond 
     ((null stanje) '())
     (
       (equal (caar stanje) (car el)) (proveri_simbol_teme_vrsta (cdar stanje) (cadr el) simbol)

     )
    (t
    (proveri_simbol_teme el (cdr stanje) simbol)
    )
    
    ))
(defun proveri_simbol_teme_vrsta(vrsta el simbol)
(cond
((null vrsta) '())
((and (equal (caar vrsta) el) (equal (cadar vrsta) simbol))
t
)
(t
(proveri_simbol_teme_vrsta (cdr vrsta) el simbol)
)
)



)

(defun gornji_sused(preCvor cvor)
    (let*
        (
            (susedL (cons (1- (car cvor)) (list (1- (cadr cvor))) ) )
            (susedI (cons (1- (car cvor)) (list (cadr cvor)) ) )
            (susedD (cons (1- (car cvor)) (list (1+ (cadr cvor))) ) )
        )
        (or
            (equal preCvor susedL)
            (equal preCvor susedI)
            (equal preCvor susedD)
        )
    )
)

(defun nadji_element(cvor cvorovi)
    (cond
        (
            (null cvorovi)
            '()
        )
        (
            (equal cvor (car cvorovi))
            t
        )
        (
            t
            (nadji_element cvor (cdr cvorovi))
        )
    )
)
;; III FAZA PROJEKTA
(defun minimax (stanje dubina simbol)
 (let 
    (
        (lp (nova-stanja stanje simbol))
        (f (if (equal simbol 'X) (car max-stanje) 'min-stanje))
    )
    (cond 
        (
            (or (zerop dubina) (null lp))
            (list stanje (proceni-stanje stanje stanje))
        )
        (t (apply f (list (mapcar (lambda (x) (minimax x (1- dubina) (promeni_simbol simbol))) lp))))
    )
 )
)

(defun promeni_simbol(simbol)
    (cond 
        (
            (equal simbol 'X)
            'O
        )
        (t
            'X
        )
    
    )
)

(defun max-stanje (listastanja)
    (max-stanje-i (cdr listastanja) (car listastanja))
) 
(defun max-stanje-i (listastanja stanje-vrednost)
    (cond 
        (
            (null listastanja) 
            stanje-vrednost
        )
        (
            (> (cadar listastanja) (cadr stanje-vrednost))
            (max-stanje-i (cdr listastanja) (car listastanja))
        )
        (t 
            (max-stanje-i (cdr listastanja) stanje-vrednost)
        )
    )
 )
(defun min-stanje (listastanja)
    (min-stanje-i (cdr listastanja) (car listastanja))
) 
(defun min-stanje-i (listastanja stanje-vrednost)
    (cond 
        (
            (null listastanja) 
            stanje-vrednost
        )
        (
            (< (cadar listastanja) (cadr stanje-vrednost))
            (min-stanje-i (cdr listastanja) (car listastanja))
        )
        (t 
            (min-stanje-i (cdr listastanja) stanje-vrednost)
        )
    )
)

 (defun nova-stanja(stanje simbol) 

     (sva_sledeca_stanja (vrati_listu_pozicija_praznih stanje) simbol stanje)
 )

(defun proceni-stanje (stanje pomstanje)
     (cond
        (
            (null stanje)
            0
        )
        (t
            (+ (proceni-stanje-vrsta (caar stanje) (cdr (car stanje)) pomstanje)  (proceni-stanje (cdr stanje) pomstanje ))
        )
     )
)
;;pomocna funkcija koju smo koristili za proveru generisanja cinjenica
(defun proveri()
    (setq *JULIJANV2-FACTS* (formiraj_listu_cinjenica stanje))
    (prepare-knowledge *JULIJANV2-RULES* *JULIJANV2-FACTS* 2)
   ;; (print (infer '(SusedX ?brojsuseda)))
    (print (odredi_max (infer '(SusedX ?brojsuseda)) 1))
    
)
;;pomocna funkcija koja se zove iz heuristkike koja odredjuje maksimalnu vrednost prosledjenog upita(infera) odnosno odredjuje maksimalni broj suseda koje bi neko stanje imalo,sto koristimo u heuristici
(defun odredi_max(upit vrednost)
     (cond ((null upit) vrednost)
        (t (if (> (cadaar upit) vrednost) (odredi_max (cdr upit) (cadaar upit)) (odredi_max (cdr upit) vrednost)))
    )
)
(defun proceni-stanje-vrsta(rbrvrste vrsta pomstanje)
    
    (cond 
        (
            (null vrsta)
            0
        )
        (
            (or (equal (car (cdr (car vrsta)))  -1)  (equal (car (cdr (car vrsta)))  0))
            (+ 0 (proceni-stanje-vrsta rbrvrste (cdr vrsta) pomstanje))
        )
         (
              (proveri_element_p (cons rbrvrste (list (car (car vrsta)))) lista_temena)
              (if (and (equal (car (cdr (car vrsta)))  'X)  (> (length (nadji_susede (formiraj_potez rbrvrste (caar vrsta)) 'O pomstanje))0)) 
                    502 
                  (if (and (equal (car (cdr (car vrsta)))  'O)  (> (length (nadji_susede (formiraj_potez rbrvrste (caar vrsta)) 'X pomstanje)) 0) )
                        -502
                        (cond
                            (
                                (equal (car (cdr (car vrsta)))  'X)
                                (+ (length (nadji_susede (formiraj_potez rbrvrste (caar vrsta)) 'X pomstanje)) (proceni-stanje-vrsta rbrvrste (cdr vrsta) pomstanje))
                            )
                            (t
                                (-  (proceni-stanje-vrsta rbrvrste (cdr vrsta) pomstanje)  (length (nadji_susede (formiraj_potez rbrvrste (caar vrsta)) 'O pomstanje)) )
                            
                            )
                        )
                  )
                
            
              )

         )
        (
            (equal (car (cdr (car vrsta)))  'X)
             (+ (length (nadji_susede (formiraj_potez rbrvrste (caar vrsta)) 'X pomstanje)) (proceni-stanje-vrsta rbrvrste (cdr vrsta) pomstanje))
        )
        (t
            (-  (proceni-stanje-vrsta rbrvrste (cdr vrsta) pomstanje)  (length (nadji_susede (formiraj_potez rbrvrste (caar vrsta)) 'O pomstanje)) )
           
        )
    
    )
)


(defun proveri_kraj(stanje simbol)
    (or (proveri_viljuska_stanje stanje simbol) (most simbol lista_temena stanje) (proveri_prsten_cvorovi (vrati_sve simbol stanje)))
)
;;nova heuristika gde imamo postavljanje cinjenica na osnovu zadatog stanja i vraca odgovarajuce vrednosti(brani drugog igraca da pobedi),ili spaja sto vise svojih simbola uz pomoc odredi_max
(defun heuristika(stanje simbol)
    
        (setq *JULIJANV2-FACTS* (formiraj_listu_cinjenica stanje))
        (prepare-knowledge *JULIJANV2-RULES* *JULIJANV2-FACTS* 2) 
            (cond 
                (
                    (>= (count-results '(PobedioX)) 1) 
                    10000
                )
                (
                    (>= (count-results '(PobedioO)) 1) 
                    -10000
                )
                (
                    (equal simbol 'X)
                    (* (odredi_max (infer '(SusedX ?brojsuseda)) 1) 10)

                )
                (t 
                    
                    (* (odredi_max (infer '(SusedO ?brojsuseda)) 1) 10)
                )
            
            )

)
(defun formiraj_potez(ind1 ind2)
    
    (cons ind1 (list ind2))
)
(defun mina (a b)
  (cond
    ((eql (cadr a) 1000) b)
    ((eql (cadr b) 1000) a)
    ((eql (cadr a) -1000) minValue)
    ((eql (cadr b) -1000) minValue)
    ((< (cadr a) (cadr b))
    a
    )
    (t 
    b
    )
)
)
(defun maxa (a b)
  (cond
    ((eql (cadr a) -1000) b)
    ((eql (cadr b) -1000) a)
    ((eql (cadr a) 1000) maxValue)
    ((eql (cadr b) 1000) maxValue)
    ((> (cadr a) (cadr b))
    a
    )
    (t 
    b
    )
)
)
(defun alphabeta (cvor dubina a b simbol start)
;;   (when (or (= dubina 0) (proveri_kraj stanje simbol))  
;;     (return-from alphabeta (list cvor (heuristika cvor simbol))))
  (if (= dubina 0)
        (return-from alphabeta (list cvor (heuristika cvor simbol)))
        (if (proveri_kraj cvor simbol)
            (if (equal simbol 'X) (list cvor 1000) (list cvor -1000) )
        )
  )  
  (if (equal simbol 'X)
      (let ((value minValue))
        (dolist (child (nova-stanja cvor simbol))
          (setf pom (maxa value (alphabeta child (1- dubina) a b (promeni_simbol simbol) nil)))
          (if (> (cadr pom) (cadr value))  (setf value (if start (list child (cadr pom)) pom)))
          (setf a (maxa a value))
          (when (<= (cadr b) (cadr a))
            (return)))
        value)
      (let ((value maxValue))
        (dolist (child (nova-stanja cvor simbol))
          (setf pom (mina value (alphabeta child (1- dubina) a b (promeni_simbol simbol) nil)))
           (if (< (cadr pom) (cadr value))  (setf value (if start (list child (cadr pom)) pom)))
          (setf b (mina b value))
          (when (<= (cadr b) (cadr a))
            (return)))
        value))
)

(defun igra_kompjuter(simbol)  ;;simulacija poteza masine,gde ona u datom kodu generise neki random,odnosno nasumicni potezi

    (format t "Kompjuter igra potez ~%")
    (setq stanje (car (alphabeta stanje dubina minValue maxValue simbol t)))
    (if (proveri_viljuska_stanje stanje simbol) (setq fork 'T) (setq fork '())) 
    (if (most simbol lista_temena stanje) (setq most 'T) (setq most '()))
    (if (proveri_prsten_cvorovi (vrati_sve simbol stanje) ) (setq prsten 'T) (setq prsten '()))
    (prikazi_celu_tablu)
    (povecajfaktor) 
    (if (or fork most prsten) (format t "Kraj igre kompjuter je pobedio!~%"))
)
(defun cetri_dva (lista_stanja) 
    (cond
        (
            (null lista_stanja)
            '()
        )
        (
            (cetridva (car lista_stanja) (car lista_stanja))
            (car lista_stanja)
        )
        (
            t
            (cetri_dva (cdr lista_stanja))
        )
    )
)
(defun cetridva(stanje pomstanje)
    (cond 
        (
            (null stanje)
            '() 
        )
        (
            (and (equal (caar stanje) 4) (proveri_element_p '(2 'x) (cdar stanje)))
            (pomstanje)
        )
        (
            t
            (cetridva (cdr stanje) pomstanje)
        )
    )
)

;;(trace cetri_dva)
;;(trace !most)
;;(trace most)

;;(trace proveri_simbol_teme)
(pocni_igru)
(setq pomstanje 
    '( 
            (0 (0 -1) (1 -1) (2 -1) (3 -1) (4 -1) (5 X) (6 O) (7 X) (8 0) (9 0) (10 0) (11 -1) (12 -1) (13 -1) (14 -1) (15 -1))
            (1 (0 -1) (1 -1) (2 -1) (3 -1) (4 0) (5 X) (6 0) (7 0) (8 0) (9 0) (10 0) (11 -1) (12 -1) (13 -1) (14 -1) (15 -1))
            (2 (0 -1) (1 -1) (2 -1) (3 0) (4 0) (5 0) (6 0) (7 X) (8 X) (9 0) (10 0) (11 -1) (12 -1) (13 -1) (14 -1) (15 -1))
            (3 (0 -1) (1 -1) (2 0) (3 0) (4 0) (5 0) (6 0) (7 0) (8 0) (9 0) (10 0) (11 -1) (12 -1) (13 -1) (14 -1) (15 -1))
            (4 (0 -1) (1 0) (2 0) (3 0) (4 0) (5 0) (6 0) (7 0) (8 0) (9 0) (10 0) (11 -1) (12 -1) (13 -1) (14 -1) (15 -1))
            (5 (0 0) (1 0) (2 0) (3 0) (4 0) (5 O) (6 0) (7 O) (8 0) (9 0) (10 0) (11 -1) (12 -1) (13 -1) (14 -1) (15 -1))
            (6 (0 -1) (1 0) (2 0) (3 0) (4 0) (5 O) (6 0) (7 0) (8 O) (9 0) (10 0) (11 -1) (12 -1) (13 -1) (14 -1) (15 -1))
            (7 (0 -1) (1 -1) (2 0) (3 0) (4 0) (5 O) (6 0) (7 0) (8 0) (9 0) (10 0) (11 -1) (12 -1) (13 -1) (14 -1) (15 -1))
            (8 (0 -1) (1 -1) (2 -1) (3 0) (4 0) (5 0) (6 0) (7 0) (8 0) (9 0) (10 0) (11 -1) (12 -1) (13 -1) (14 -1) (15 -1))
            (9 (0 -1) (1 -1) (2 -1) (3 -1) (4 0) (5 0) (6 0) (7 0) (8 0) (9 O) (10 0) (11 -1) (12 -1) (13 -1) (14 -1) (15 -1))
            (10 (0 -1) (1 -1) (2 -1) (3 -1) (4 -1) (5 0) (6 0) (7 0) (8 0) (9 0) (10 0) (11 -1) (12 -1) (13 -1) (14 -1) (15 -1))
        
    ) 
)
;; (print (formiraj_listu_suseda (spoji 1 (izdvoji_elemente (cdr (car pomstanje)))) pomstanje))





