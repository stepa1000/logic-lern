(* Базовые соответствия:
   True  = Топ (1)
   False = Бот (0)
   /\    = Конъюнкция (встреча / meet / infimum)
   \/    = Дизъюнкция (соединение / join / supremum)
   ->    = Псевдодополнение (импликация Гейтинга)
   ~A    = Отрицание Гейтинга (сокращение для A -> False)
*)

Require Import Setoid.
Require Import Morphisms.

Section HeytingAlgebra.

Variables A B C : Prop.

(* ======================================================= *)
(* ПРИМЕР 1: Закон противоречия (A ⊓ ¬A = 0)              *)
(* ======================================================= *)
Theorem heyting_contradiction : A /\ ~A -> False.
Proof.
  intros h.          (* Переносим посылку в гипотезы *)
  destruct h as [hA hNotA]. (* Разделяем конъюнкцию на части *)
  unfold not in hNotA.      (* ~A раскрывается как A -> False *)
  apply hNotA.       (* Чтобы доказать False, достаточно доказать A *)
  exact hA.          (* A у нас уже есть *)
Qed.

(* ======================================================= *)
(* ПРИМЕР 2: Дистрибутивность (Упрощение формулы слева)     *)
(* Утверждение: (A ⊔ B) ⊓ A <=> A                         *)
(* ======================================================= *)
Theorem heyting_absorb : (A \/ B) /\ A <-> A.
Proof.
  split. (* Разделяем эквивалентность на две импликации: -> и <- *)
  - (* Направление -> *)
    intros h.
    destruct h as [hOr hA].
    exact hA. (* B нам даже не понадобилось *)
  - (* Направление <- *)
    intros hA.
    split.
    + left. exact hA. (* Доказываем левую часть дизъюнкции A \/ B *)
    + exact hA.
Qed.

(* ======================================================= *)
(* ЗАДАЧА 1 (Для тренировки): Псевдодополнение            *)
(* В булевой алгебре: ¬(¬A) = A.                           *)
(* В алгебре Гейтинга верно только слабое: A ⊓ ¬(¬A) = A  *)
(* Докажите закон тройного отрицания: ¬¬¬A <=> ¬A          *)
(* ======================================================= *)
Theorem triple_negation : ~~~A <-> ~A.
Proof.
  split.
  - intros hNotNotNotA hA.
    (* Подсказка: используйте hNotNotNotA, применив его к 
       доказательству двойного отрицания для A *)
    apply hNotNotNotA.
    intros hNotA.
    apply hNotA.
    exact hA.
  - intros hNotA hNotNotA.
    apply hNotNotA.
    exact hNotA.
Qed.

Lemma lNotOr : forall A B : Prop, ~ (A \/ B) -> ~ A.
Proof.
  intros A0 B0 hNotOr.
  intros hA.
  apply hNotOr.
  left.
  exact hA.
Qed.

Lemma or_commutative : forall (X Y : Prop), 
  (X \/ Y) <-> (Y \/ X).
Proof.
  intros.
  split.
  - intros hOr.
    destruct hOr as [hX | hY].
    { right.
      exact hX.
    }
    { left.
      exact hY.
    }
  - intros hOr.
    destruct hOr as [hY| hX].
    { right.
      exact hY.
    }
    { left.
      exact hX.
    }
Qed.

Lemma not_congruence : forall (P Q : Prop), 
  (P <-> Q) -> (~P <-> ~Q).
Proof.
  intros P Q.
  intros isoPQ.
  destruct isoPQ as [toQ toP].
  split.
  - intros hNotP hQ.
    pose proof (toP hQ) as hP.
    apply hNotP.
    exact hP.
  - intros hNotQ hP.
    pose proof (toQ hP) as hQ.
    apply hNotQ.
    exact hQ.
Qed.

Lemma lNotAnd : forall (A B : Prop), (~ A /\ ~ B) -> A -> False.
Proof.
  intros A0 B0.
  intros hNotAnd hA.
  destruct hNotAnd as [hNotA hNotB].
  apply hNotA.
  exact hA.
Qed.

Lemma and_commutative : forall (X Y : Prop), 
  (X /\ Y) <-> (Y /\ X).
Proof.
   intros.
   split.
   - intros hAnd.
     destruct hAnd as [hX hY].
     split.
     { exact hY. } 
     { exact hX. }
   - intros hAnd.
     destruct hAnd as [hY hX].
     split.
     { exact hX. } 
     { exact hY. }
Qed.
(* ======================================================= *)
(* ЗАДАЧА 2 (Самостоятельно): Законы Де Моргана            *)
(* В Гейтинговой структуре один из законов Де Моргана      *)
(* работает строго в обе стороны, в отличие от второго.    *)
(* Упростите/докажите: ¬(A ⊔ B) <=> ¬A ⊓ ¬B                *)
(* ======================================================= *)
Theorem demorgan_heyting : ~(A \/ B) <-> ~A /\ ~B.
Proof.
  split.
  - intros hNotOr.
    split.
    { apply (lNotOr A B).
      exact hNotOr.
    }
    { apply (lNotOr B A).
      intros hNotOrBA.
      apply hNotOr.
      apply or_commutative.
      exact hNotOrBA.
    }
  - intros hNotAnd hOr.
    destruct hOr as [hA | hB].
    { apply (lNotAnd A B).
      + exact hNotAnd.
      + exact hA.
    }
    { destruct hNotAnd as [hNotA hNotB].
      apply hNotB.
      exact hB.
    }
Qed.

(* ======================================================= *)
(* ЗАДАЧА 3 (Сложная): Законы дистрибутивности импликации   *)
(* Докажите сокращение: (A ⊔ B -> C) <=> (A -> C) ⊓ (B -> C)*)
(* ======================================================= *)
Theorem implication_distributive : (A \/ B -> C) <-> (A -> C) /\ (B -> C).
Proof.
  split.
  - intros hOrToC.
    split.
    { intros hA.
      apply hOrToC.
      left.
      exact hA.
    }
    { intros hB.
      apply hOrToC.
      right.
      exact hB.
    }
  - intros hAndToToC hOr.
    destruct hAndToToC as [hAToC hBToC].
    destruct hOr as [hA | hB].
    { apply hAToC.
      exact hA.
    }
    { apply hBToC.
      exact hB.
    }
Qed.

End HeytingAlgebra.
