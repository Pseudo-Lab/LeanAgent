import Mathlib
import Aesop

set_option maxHeartbeats 0

open Filter Topology Real


theorem putnam_1995_a3
(relation : (Fin 9 → ℤ) → (Fin 9 → ℤ) → Prop)
(digits_to_num : (Fin 9 → ℤ) → ℤ)
(hdigits_to_num : digits_to_num = fun dig => ∑ i : Fin 9, (dig i) * 10^i.1)
(hrelation : ∀ d e : (Fin 9 → ℤ), relation d e ↔ (∀ i : Fin 9, d i < 10 ∧ d i ≥ 0 ∧ e i < 10 ∧ e i ≥ 0) ∧ (∀ i : Fin 9, 7 ∣ (digits_to_num (fun j : Fin 9 => if j = i then e j else d j))))
: ∀ d e f : (Fin 9 → ℤ), ((relation d e) ∧ (relation e f)) → (∀ i : Fin 9, 7 ∣ d i - f i) := by
  classical
  intro d e f hrel i
  have hde :
      ∀ k : Fin 9,
        7 ∣ digits_to_num (fun j : Fin 9 => if j = k then e j else d j) :=
    ((hrelation d e).mp hrel.1).2
  have hef :
      ∀ k : Fin 9,
        7 ∣ digits_to_num (fun j : Fin 9 => if j = k then f j else e j) :=
    ((hrelation e f).mp hrel.2).2
  have hreplace (a b : Fin 9 → ℤ) (k : Fin 9) :
      digits_to_num (fun j : Fin 9 => if j = k then b j else a j) =
        digits_to_num a + (b k - a k) * 10 ^ k.1 := by
    rw [hdigits_to_num]
    calc
      (∑ j : Fin 9, (if j = k then b j else a j) * 10 ^ j.1) =
          ∑ j : Fin 9,
            (a j * 10 ^ j.1 +
              if j = k then (b k - a k) * 10 ^ j.1 else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h : j = k
        · subst j
          simp
          ring
        · simp [h]
      _ = (∑ j : Fin 9, a j * 10 ^ j.1) +
          (b k - a k) * 10 ^ k.1 := by
        rw [Finset.sum_add_distrib]
        simp
  have pair_dvd (a b : Fin 9 → ℤ)
      (hab : ∀ k : Fin 9,
        7 ∣ digits_to_num (fun j : Fin 9 => if j = k then b j else a j)) :
      7 ∣ digits_to_num a + digits_to_num b := by
    have hs :
        7 ∣ ∑ k : Fin 9,
          digits_to_num (fun j : Fin 9 => if j = k then b j else a j) := by
      apply Finset.dvd_sum
      intro k hk
      exact hab k
    have hdiff :
        (∑ k : Fin 9, (b k - a k) * 10 ^ k.1) =
          digits_to_num b - digits_to_num a := by
      rw [hdigits_to_num]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    have hsum :
        (∑ k : Fin 9,
          digits_to_num (fun j : Fin 9 => if j = k then b j else a j)) =
          8 * digits_to_num a + digits_to_num b := by
      simp_rw [hreplace a b]
      rw [Finset.sum_add_distrib, hdiff]
      norm_num [Fin.sum_univ_succ] <;> ring
    rw [hsum] at hs
    have h7 : (7 : ℤ) ∣ 7 * digits_to_num a :=
      ⟨digits_to_num a, rfl⟩
    have hh := dvd_sub hs h7
    convert hh using 1 <;> ring
  have hDE : 7 ∣ digits_to_num d + digits_to_num e :=
    pair_dvd d e hde
  have hboth :
      7 ∣
        digits_to_num (fun j : Fin 9 => if j = i then e j else d j) +
        digits_to_num (fun j : Fin 9 => if j = i then f j else e j) :=
    dvd_add (hde i) (hef i)
  have hp : 7 ∣ (f i - d i) * 10 ^ i.1 := by
    have ht := dvd_sub hboth hDE
    rw [hreplace d e i, hreplace e f i] at ht
    convert ht using 1 <;> ring
  have hcoprime :
      ∃ u v : ℤ, u * 10 ^ i.1 + v * 7 = 1 := by
    fin_cases i <;>
      first
      | exact ⟨1, 0, by norm_num⟩
      | exact ⟨5, -7, by norm_num⟩
      | exact ⟨4, -57, by norm_num⟩
      | exact ⟨6, -857, by norm_num⟩
      | exact ⟨2, -2857, by norm_num⟩
      | exact ⟨3, -42857, by norm_num⟩
      | exact ⟨1, -142857, by norm_num⟩
      | exact ⟨5, -7142857, by norm_num⟩
      | exact ⟨4, -57142857, by norm_num⟩
  have cancel (x c : ℤ)
      (hc : ∃ u v : ℤ, u * c + v * 7 = 1)
      (hx : 7 ∣ x * c) : 7 ∣ x := by
    rcases hc with ⟨u, v, huv⟩
    rcases hx with ⟨q, hq⟩
    refine ⟨u * q + v * x, ?_⟩
    calc
      x = 1 * x := by ring
      _ = (u * c + v * 7) * x := by rw [huv]
      _ = u * (x * c) + v * 7 * x := by ring
      _ = u * (7 * q) + v * 7 * x := by rw [hq]
      _ = 7 * (u * q + v * x) := by ring
  have hfd : 7 ∣ f i - d i :=
    cancel (f i - d i) (10 ^ i.1) hcoprime hp
  rcases hfd with ⟨q, hq⟩
  refine ⟨-q, ?_⟩
  calc
    d i - f i = -(f i - d i) := by ring
    _ = -(7 * q) := by rw [hq]
    _ = 7 * (-q) := by ring

#check _root_.putnam_1995_a3
#print axioms _root_.putnam_1995_a3
