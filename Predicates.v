Section PredicateLogic.

(* Объявим произвольный тип объектов U (Universe), 
   над которым мы будем строить наши предикаты. *)
Variable U : Type.
Variables P Q : U -> Prop.
Variable R : Prop. (* Независимое высказывание *)

(* ======================================================= *)
(* ШПАРГАЛКА ПО ТАКТИКАМ ДЛЯ КВАНТОРОВ:                    *)
(* 1. Если forall в ЦЕЛИ: пишите 'intros x.', где x - имя  *)
(*    произвольного объекта из U.                          *)
(* 2. Если forall в ГИПОТЕЗЕ (H : forall x, ...):          *)
(*    пишите 'apply (H x_concrete).' или 'specialize (H x)'.*)
(* 3. Если exists в ЦЕЛИ: вы обязаны предъявить конкретный *)
(*    объект x через тактику 'exists x.'.                  *)
(* 4. Если exists в ГИПОТЕЗЕ (H : exists x, ...):          *)
(*    пишите 'destruct H as [x hX].', чтобы получить       *)
(*    конкретный объект и свидетельство его свойства.      *)
(* ======================================================= *)


(* ======================================================= *)
(* ПРИМЕР 1: Дистрибутивность квантора всеобщности         *)
(* Утверждение: (∀x, P(x) ⊓ Q(x)) <=> (∀x, P(x)) ⊓ (∀x, Q(x))*)
(* ======================================================= *)
Theorem forall_distributive_and : 
  (forall x : U, P x /\ Q x) <-> (forall x : U, P x) /\ (forall x : U, Q x).
Proof.
  split.
  - intros hAll. split.
    + intros x. (* Нам нужно доказать P x для любого x *)
      (* Применяем hAll к нашему конкретному x, чтобы извлечь конъюнкцию *)
      destruct (hAll x) as [hP hQ].
      exact hP.
    + intros x.
      destruct (hAll x) as [hP hQ].
      exact hQ.
  - intros hAnd x.
    destruct hAnd as [hAllP hAllQ].
    split.
    + apply hAllP. (* hAllP работает для любого x, значит сработает и для нашего *)
    + apply hAllQ.
Qed.


(* ======================================================= *)
(* ЗАДАЧА 1: Вынесение независимой константы               *)
(* Если высказывание R не зависит от переменной x, то      *)
(* квантор существования можно вносить внутрь конъюнкции.  *)
(* Докажите: ∃x, (R ⊓ P(x)) <=> R ⊓ (∃x, P(x))              *)
(* ======================================================= *)
Theorem exists_distributive_and_const :
  (exists x : U, R /\ P x) <-> R /\ (exists x : U, P x).
Proof.
  split.
  - intros hAnd.
    destruct hAnd as [hx hRAndPhx].
    destruct hRAndPhx as [hR hPx].
    split.
    { exact hR.
    }
    { exists hx.
      exact hPx.
    }
  - intros hRAndP.
    destruct hRAndP as [hR hPx].
    destruct hPx as [hx hPhx].
    exists hx.
    split.
    { exact hR.
    }
    { exact hPhx.
    }
Qed.


(* ======================================================= *)
(* ЗАДАЧА 2: Связь кванторов (Асимметрия интуиционизма)    *)
(* В классической логике ¬(∃x, P(x)) эквивалентно ∀x, ¬P(x).*)
(* В интуиционистской логике Гейтинга это верно только      *)
(* в одну сторону! Докажите её.                            *)
(* ======================================================= *)
Theorem not_exists_to_forall :
  ~(exists x : U, P x) -> (forall x : U, ~ P x).
Proof.
  intros hPx hx.
  intros hPx2.
  destruct hPx.
  exists hx.
  exact hPx2.
Qed.


(* ======================================================= *)
(* ЗАДАЧА 3 (Сложная): «Парадокс» пьющего (Ослабленный)      *)
(* Классическая теорема ∃x, (P(x) -> ∀y, P(y)) ложна в      *)
(* интуиционистской логике. Но её двойное отрицание истинно!*)
(* Докажите её: ¬¬(∃x, (P(x) -> ∀y, P(y)))                 *)
(* Подсказка: Раскройте отрицания и используйте тактики,   *)
(* которые вы отточили на задаче с тройным отрицанием.    *)
(* ======================================================= *)
Theorem constructive_drinking_paradox (x0 : U) :
  ~ ~ (exists x : U, P x -> forall y : U, P y).
Proof.
  intros hNotPxToPy.
  apply hNotPxToPy.
  exists x0.
  intros hPx0 y.
  exfalso.
  apply hNotPxToPy.
  exists x0.
  intros hPy y0.
  exfalso.
  apply hNotPxToPy.
  exists y.
  intros hPy2 y1.
  Admitted.

(* Универсальное квантование по предикатам (Prop) *)
Theorem second_order_challenge :
  forall P : Prop, (forall Q : Prop, (P -> Q) -> Q) <-> P.
Proof.
  intros P0. split.
  - intros hAll.
    (* Вместо слепого apply, специализируем гипотезу конкретным типом P *)
    specialize (hAll P0).
    (* Теперь hAll превратилась в: (P -> P) -> P *)
    
    apply hAll.
    (* Цель изменилась на: P -> P *)
    
    intros hP. exact hP.
    
  - (* Обратная ветка теперь покажется вам очень простой *)
    intros hP Q0 hPToQ.
    apply hPToQ.
    exact hP.
Qed.

End PredicateLogic.

Section HigherOrderLogic.

Variable U : Type.
(* Бинарный предикат (2-й степени) *)
Variable R : U -> U -> Prop.

(* ======================================================= *)
(* СЛОЖНАЯ ЗАДАЧА: Перестановка кванторов                  *)
(* Докажите: Если существует y, который находится в        *)
(* отношении R со всеми x, то для любого x существует      *)
(* такой y, что R x y выполнено.                           *)
(* ======================================================= *)
Theorem quantifiers_commute_weak :
  (exists y : U, forall x : U, R x y) -> (forall x : U, exists y : U, R x y).
Proof.
  intros hRxy hy.
  destruct hRxy as [hx hRxhx].
  exists hx.
  apply hRxhx.
Qed.

End HigherOrderLogic.

