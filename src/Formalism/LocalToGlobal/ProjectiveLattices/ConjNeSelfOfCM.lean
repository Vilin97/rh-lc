module

public import Formalism.LocalToGlobal.ProjectiveLattices.CrudeMin
public import Formalism.LocalToGlobal.ProjectiveLattices.CrudeBase
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.ProjectiveLattices.CrudeOrd
public import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.LocalToGlobal.ProjectiveLattices.CrudeDiv

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.Crude

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {k : Type} [CommRing k] {d n : ℕ}

theorem div_Lin_add (b : Fin n) (v : Fin d → k) (f g : PS k n d) :
    Lin b v (f + g) = Lin b v f + Lin b v g := by
  simp only [Lin, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem div_Lin_mul (b : Fin n) (v : Fin d → k) (f g : PS k n d) :
    Lin b v (f * g) = Lin b v f * g + f * Lin b v g := by
  simp only [Lin, Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul,
    Finset.mul_sum]
  rw [add_comm]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => ?_ <;> ring

theorem div_Lin_C (b : Fin n) (v : Fin d → k) (c : k) : Lin b v (C c : PS k n d) = 0 := by
  simp [Lin, MvPowerSeries.pderiv_C]

theorem Lin_linForm (b b' : Fin n) (v w : Fin d → k) :
    Lin b v (∑ j : Fin d, C (w j) * (X (b', j) : PS k n d)) =
      C (if b = b' then ∑ j : Fin d, v j * w j else 0) := by
  unfold Lin
  by_cases h : b = b'
  · subst h

    simp [MvPowerSeries.pderiv_X, MvPowerSeries.pderiv_C, Derivation.leibniz, Finset.mul_sum,
    map_sum, Pi.single_apply, Prod.ext_iff]
  · simp [MvPowerSeries.pderiv_X, MvPowerSeries.pderiv_C, Derivation.leibniz, Pi.single_apply,
      Prod.ext_iff, h]

theorem div_Lin_aeval {ι : Type} [DecidableEq ι] (cp : ι → Fin n) (u : ι → Fin d → k) (φ : ι → PS k n d)
    (l : ι) (hl : ∀ l', Lin (cp l) (u l) (φ l') = C (if l = l' then 1 else 0)) (Q : MvPolynomial ι k) :
    Lin (cp l) (u l) (MvPolynomial.aeval φ Q) = MvPolynomial.aeval φ (MvPolynomial.pderiv l Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C, MvPolynomial.pderiv_C, map_zero, MvPowerSeries.algebraMap_apply]
    simpa using div_Lin_C (cp l) (u l) a
  | add p q hp hq => rw [map_add (f := _), div_Lin_add, hp, hq, map_add (f := _), map_add (f := _)]
  | mul_X p i hp =>
    rw [map_mul, div_Lin_mul, hp, MvPolynomial.aeval_X, hl, Derivation.leibniz, MvPolynomial.pderiv_X]
    by_cases h : l = i
    · subst h
      simp
      ring
    · simp [h, Pi.single_apply]
      ring

theorem div_Lin_iter_aeval {ι : Type} [DecidableEq ι] (cp : ι → Fin n) (u : ι → Fin d → k) (φ : ι → PS k n d)
    (l : ι) (hl : ∀ l', Lin (cp l) (u l) (φ l') = C (if l = l' then 1 else 0)) (t : ℕ) (Q : MvPolynomial ι k) :
    (Lin (cp l) (u l))^[t] (MvPolynomial.aeval φ Q) = MvPolynomial.aeval φ ((MvPolynomial.pderiv l)^[t] Q) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, div_Lin_aeval cp u φ l hl]

theorem div_LinMon_aeval {ι : Type} [Fintype ι] [DecidableEq ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (φ : ι → PS k n d) (Good : Set ι)
    (hdual : ∀ l ∈ Good, ∀ l', Lin (cp l) (u l) (φ l') = C (if l = l' then 1 else 0))
    (a : ι →₀ ℕ) (ha : ∀ l, a l ≠ 0 → l ∈ Good) (Q : MvPolynomial ι k) :
    LinMon cp u a (MvPolynomial.aeval φ Q) = MvPolynomial.aeval φ
      ((Finset.univ : Finset ι).toList.foldr (fun l g => (MvPolynomial.pderiv l)^[a l] g) Q) := by
  unfold LinMon
  generalize (Finset.univ : Finset ι).toList = L
  induction L with
  | nil => rfl
  | cons l L ih =>
    simp only [List.foldr_cons]
    rw [ih]
    by_cases h0 : a l = 0
    · rw [h0]
      rfl
    · exact div_Lin_iter_aeval cp u φ l (hdual l (ha l h0)) (a l) _

theorem div_constCoeff_aeval {ι : Type} (φ : ι → PS k n d) (hφ0 : ∀ i, constantCoeff (φ i) = 0)
    (Q : MvPolynomial ι k) : constantCoeff (MvPolynomial.aeval φ Q) = MvPolynomial.constantCoeff Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [MvPowerSeries.algebraMap_apply]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => simp [hp, hφ0]

theorem div_iter_pderiv_monomial {ι : Type} [DecidableEq ι] (i : ι) (t : ℕ) (s : ι →₀ ℕ) (c : k) :
    (MvPolynomial.pderiv i)^[t] (MvPolynomial.monomial s c) =
      MvPolynomial.monomial (s - Finsupp.single i t) (c * ((s i).descFactorial t : k)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 : s - Finsupp.single i t - Finsupp.single i 1 = s - Finsupp.single i (t + 1) := by
      ext j
      first
        | (simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]; split_ifs <;> omega)
        | (simp only [Finsupp.tsub_apply, Finsupp.single_apply]; split_ifs <;> omega)
        | (simp [Finsupp.single_apply]; split_ifs <;> omega)
    have h2 : (s - Finsupp.single i t) i = s i - t := by
      first
        | simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
        | simp
    rw [Function.iterate_succ_apply', ih, MvPolynomial.pderiv_monomial, h1, h2,
      Nat.descFactorial_succ]
    congr 1
    push_cast
    ring

theorem div_listSum_apply_of_notMem {ι : Type} (a : ι →₀ ℕ) (L : List ι) (l : ι) (hl : l ∉ L) :
    (L.map fun l' => Finsupp.single l' (a l')).sum l = 0 := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.mem_cons, not_or] at hl
    simp [Finsupp.single_apply, Ne.symm hl.1, ih hl.2]

theorem div_fold_monomial {ι : Type} [DecidableEq ι] (a : ι →₀ ℕ) (L : List ι) (hL : L.Nodup) (s : ι →₀ ℕ)
    (c : k) :
    L.foldr (fun l g => (MvPolynomial.pderiv l)^[a l] g) (MvPolynomial.monomial s c) =
      MvPolynomial.monomial (s - (L.map fun l => Finsupp.single l (a l)).sum)
        (c * (L.map fun l => ((s l).descFactorial (a l) : k)).prod) := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.nodup_cons] at hL
    rw [List.foldr_cons, ih hL.2, div_iter_pderiv_monomial]
    have hx : (s - (L.map fun l => Finsupp.single l (a l)).sum) x = s x := by
      rw [Finsupp.tsub_apply, div_listSum_apply_of_notMem a L x hL.1, Nat.sub_zero]
    simp only [List.map_cons, List.sum_cons, List.prod_cons, hx]
    congr 1
    · rw [tsub_tsub, add_comm]
    · ring

theorem linMon_aeval_monomial {ι : Type} [Fintype ι] [DecidableEq ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (φ : ι → PS k n d) (hφ0 : ∀ i, constantCoeff (φ i) = 0) (Good : Set ι)
    (hdual : ∀ l ∈ Good, ∀ l', Lin (cp l) (u l) (φ l') = C (if l = l' then 1 else 0))
    (a α : ι →₀ ℕ) (ha : ∀ l, a l ≠ 0 → l ∈ Good) :
    constantCoeff (LinMon cp u a (MvPolynomial.aeval φ (MvPolynomial.monomial α (1 : k)))) =
      if a = α then ((α.prod fun _ e => e.factorial : ℕ) : k) else 0 := by
  classical
  rw [div_LinMon_aeval cp u φ Good hdual a ha, div_fold_monomial a _ (Finset.nodup_toList _),
    div_constCoeff_aeval φ hφ0, MvPolynomial.constantCoeff_monomial]
  have hLs : ∀ (M : Type) [AddCommMonoid M] (f : ι → M),
      ((Finset.univ : Finset ι).toList.map f).sum = ∑ l, f l := fun M _ f => by
    rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
    rfl
  have hLp : ∀ (M : Type) [CommMonoid M] (f : ι → M),
      ((Finset.univ : Finset ι).toList.map f).prod = ∏ l, f l := fun M _ f => by
    rw [← Multiset.prod_coe, ← Multiset.map_coe, Finset.coe_toList]
    rfl
  have hS : ((Finset.univ : Finset ι).toList.map fun l => Finsupp.single l (a l)).sum = a := by
    rw [hLs]
    ext j
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
  have hP : ((Finset.univ : Finset ι).toList.map fun l => ((α l).descFactorial (a l) : k)).prod =
      ∏ l, ((α l).descFactorial (a l) : k) := hLp k _
  rw [hS, hP, one_mul]
  by_cases hEq : a = α
  · subst hEq
    rw [tsub_self, if_pos rfl, if_pos rfl, Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero)]
    push_cast
    exact Finset.prod_congr rfl fun l _ => by rw [Nat.descFactorial_self]
  · rw [if_neg hEq]
    split_ifs with h0
    · have hle : α ≤ a := tsub_eq_zero_iff_le.mp h0
      obtain ⟨l, hl⟩ : ∃ l, α l < a l := by
        by_contra hcon
        push_neg at hcon
        exact hEq (le_antisymm (Finsupp.le_def.mpr hcon) hle)
      exact Finset.prod_eq_zero (Finset.mem_univ l)
        (by rw [Nat.descFactorial_eq_zero_iff_lt.mpr hl, Nat.cast_zero])
    · rfl

end Formalism.L2.Pj.Crude
end
end
end

-- Source module: Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open MvPowerSeries NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} [StarRing (𝓞 E)]

def SatDir (T : CDVR) {d : ℕ} (uvec : Lt1 Dw → Fin d → T.Fr) : Prop :=
  ∀ τ : E →+* ℂ, ∃ W : Fin (Dw.mult τ) → Fin d → T.V,
    ∀ i i' : Fin (Dw.mult τ), ∑ j, uvec ⟨τ, i'⟩ j * algebraMap T.V T.Fr (W i j) = if i' = i then 1 else 0


variable (Dw) in
def DomW (a : (E →+* ℂ) × ℕ → ℕ) : Prop := Crude.Dom Dw.mult (fun τ i => a (τ, i))

def crudeBd {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (D : ℕ) : ℝ :=
  (ramOverZ la : ℝ) * (D : ℝ) / ((resCharOf la : ℝ) - 1)

omit [StarRing (𝓞 E)] in
theorem conj_ne_self_of_CM (τ : E →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := by
  haveI := NumberField.IsCMField.isTotallyComplex E
  intro hτ
  have hc := NumberField.IsTotallyComplex.isComplex (NumberField.InfinitePlace.mk τ)
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex, NumberField.InfinitePlace.isReal_mk_iff] at hc
  exact hc hτ

theorem Crude.le_degree {σ : Type} (α : σ →₀ ℕ) (s : σ) : α s ≤ α.degree := by
  by_cases hs : s ∈ α.support
  · have hd : α.degree = ∑ i ∈ α.support, α i := rfl
    rw [hd]
    exact Finset.single_le_sum (fun i _ => Nat.zero_le (α i)) hs
  · have h0 : α s = 0 := by simpa using hs
    rw [h0]
    exact Nat.zero_le _


omit [IsCMField E] [StarRing (𝓞 E)] in
variable (Dw) in
def colP {n : ℕ} (hn : Fintype.card (Lt1 Dw) ≤ n) : Lt1 Dw → Fin n :=
  fun p => Fin.castLE hn (Fintype.equivFin (Lt1 Dw) p)


open Classical in
variable (Dw) in
def P1 (T : CDVR) (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (hn : Fintype.card (Lt1 Dw) ≤ n) :
    MvPolynomial (LtN Dw n) T.Fr :=
  MvPolynomial.map (Int.castRingHom T.Fr) (Crude.Pmin Dw.mult n (colP Dw hn) (fun τ i => a (τ, i)))


open Classical in
variable (Dw) in
def fact1 (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (hn : Fintype.card (Lt1 Dw) ≤ n) : ℕ :=
  (Crude.diagExp Dw.mult n (colP Dw hn) (fun τ i => a (τ, i))).prod fun _ t => t.factorial

def crudeInf {T : CDVR} {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB T.Fr d O) (h : PS T.Fr 2 d) (w0 : O)
    (k : ℕ) (uvec : Lt1 Dw → Fin d → T.Fr) (e : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : EReal :=
  ⨅ (P : MvPolynomial (LtN Dw n) T.Fr) (_ : P ∈ FFV (Dw := Dw) T a n) (f : PS T.Fr n d) (_ : IsIntPS T f),
    nval T.V e (nabValN B T.Fr h w0 k f (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => uvec ⟨ℓ.1, ℓ.2.1⟩) P)

private theorem ordGe_prod_lemma (T : CDVR) {n d : ℕ} {ι : Type} (φ : ι → PS T.Fr n d)
    (hφ : ∀ i, constantCoeff (φ i) = 0) (α : ι →₀ ℕ) :
    Crude.OrdGe α.degree (α.prod fun i e => φ i ^ e) := by
  classical
  have hpow : ∀ i (e : ℕ), Crude.OrdGe e (φ i ^ e) := by
    intro i e
    induction e with
    | zero => exact Crude.cro_ordGe_zero (φ i ^ 0)
    | succ e ih =>
      rw [pow_succ]
      exact Crude.OrdGe.mul ih ((Crude.ordGe_one_iff _).2 (hφ i))
  have hd : α.degree = ∑ i ∈ α.support, α i := rfl
  rw [hd]
  unfold Finsupp.prod
  generalize α.support = s
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty, Finset.prod_empty]
    exact Crude.cro_ordGe_zero _
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact Crude.OrdGe.mul (hpow a (α a)) ih

theorem crude_val {T : CDVR} {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB T.Fr d O) (h : PS T.Fr 2 d)
    (hg : B.IsCanonGauge T.Fr h) (w0 : O) (k : ℕ) (uvec : Lt1 Dw → Fin d → T.Fr) (hsat : SatDir T uvec)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ha : DomW Dw a) (hn : Fintype.card (Lt1 Dw) ≤ n) :
    P1 Dw T a hn ∈ FFV (Dw := Dw) T a n ∧ ∃ f : PS T.Fr n d, IsIntPS T f ∧ Crude.OrdGe (DF Dw a) f ∧
      nabValN B T.Fr h w0 k f (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => uvec ⟨ℓ.1, ℓ.2.1⟩) (P1 Dw T a hn) =
        (fact1 Dw a hn : T.Fr) := by
  classical
  have hβ : Function.Injective (colP Dw hn) := fun p q hpq =>
    (Fintype.equivFin (Lt1 Dw)).injective (Fin.castLE_injective hn hpq)
  set α := Crude.diagExp Dw.mult n (colP Dw hn) (fun τ i => a (τ, i)) with hαdef
  have hdeg : α.degree = DF Dw a := by rw [hαdef, Crude.diagExp_degree]; rfl
  have hcoeff : (P1 Dw T a hn).coeff α = 1 := Crude.Pmin_coeff_diag (k := T.Fr) (hβ := hβ) (ha := ha)
  have hαmem : α ∈ (P1 Dw T a hn).support := by
    rw [MvPolynomial.mem_support_iff, hcoeff]; exact one_ne_zero
  refine ⟨?_, ?_⟩
  · show MvPolynomial.map (Int.castRingHom T.Fr) (Crude.Pmin Dw.mult n (colP Dw hn) (fun τ i => a (τ, i))) ∈
      HaO Dw.mult n T.Fr (algebraMap T.V T.Fr).range ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))
    exact Crude.Pmin_mem (O := (algebraMap T.V T.Fr).range) (cc := ComplexEmbedding.conjugate)
      (isX := InPsi H) (hcc := fun τ _ => conj_ne_self_of_CM τ) (hβ := hβ) (ha := ha)

  have hsat' : ∀ τ : E →+* ℂ, ∃ W : Fin (Dw.mult τ) → Fin d → T.V, ∀ i i' : Fin (Dw.mult τ),
      ∑ j, uvec ⟨τ, i'⟩ j * algebraMap T.V T.Fr (W i j) = if i' = i then 1 else 0 := hsat
  choose W hW using hsat'
  let φV : LtN Dw n → PS T.V n d := fun ℓ =>
    if (∃ i, colP Dw hn ⟨ℓ.1, i⟩ = ℓ.2.2) then ∑ j, C (W ℓ.1 ℓ.2.1 j) * X (ℓ.2.2, j) else 0
  let φ : LtN Dw n → PS T.Fr n d := fun ℓ =>
    if (∃ i, colP Dw hn ⟨ℓ.1, i⟩ = ℓ.2.2) then
      ∑ j, C (algebraMap T.V T.Fr (W ℓ.1 ℓ.2.1 j)) * X (ℓ.2.2, j) else 0
  have hmapφ : ∀ ℓ, MvPowerSeries.map (algebraMap T.V T.Fr) (φV ℓ) = φ ℓ := by
    intro ℓ
    simp only [φV, φ]
    split_ifs <;> simp [map_sum]
  have hφ0 : ∀ ℓ, constantCoeff (φ ℓ) = 0 := by
    intro ℓ
    simp only [φ]
    split_ifs <;> simp [map_sum]
  have hdual : ∀ l ∈ Crude.GoodL Dw.mult n (colP Dw hn), ∀ l',
      Crude.Lin ((fun ℓ : LtN Dw n => ℓ.2.2) l) ((fun ℓ : LtN Dw n => uvec ⟨ℓ.1, ℓ.2.1⟩) l) (φ l') =
        C (if l = l' then 1 else 0) := by
    rintro ⟨τ, i0, b⟩ ⟨i, hi⟩ ⟨τ', i', b'⟩
    simp only [φ]
    dsimp only at hi ⊢
    by_cases hg : ∃ i'', colP Dw hn ⟨τ', i''⟩ = b'
    · rw [if_pos hg, Crude.Lin_linForm]
      congr 1
      by_cases hbb : b = b'
      · subst hbb
        obtain ⟨i'', hi''⟩ := hg
        have hp : (⟨τ, i⟩ : Lt1 Dw) = ⟨τ', i''⟩ := hβ (hi.trans hi''.symm)
        obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.1 hp
        rw [if_pos rfl, hW τ i' i0]
        by_cases h : i0 = i'
        · subst h; simp
        · rw [if_neg h, if_neg]
          intro hl
          cases hl
          exact h rfl
      · rw [if_neg hbb, if_neg]
        intro hl
        cases hl
        exact hbb rfl
    · rw [if_neg hg, if_neg]
      · simpa using Crude.div_Lin_C (n := n) b (uvec ⟨τ, i0⟩) (0 : T.Fr)
      · intro hl
        cases hl
        exact hg ⟨i, hi⟩
  obtain ⟨f, hfdef⟩ : ∃ f : PS T.Fr n d, f = MvPolynomial.aeval φ (MvPolynomial.monomial α (1 : T.Fr)) :=
    ⟨_, rfl⟩
  have hfprod : f = α.prod fun ℓ e => φ ℓ ^ e := by
    rw [hfdef, MvPolynomial.aeval_monomial, map_one, one_mul]
  have hfint : IsIntPS T f := by
    intro m
    have hmap : f = MvPowerSeries.map (algebraMap T.V T.Fr) (α.prod fun ℓ e => φV ℓ ^ e) := by
      rw [hfprod]
      unfold Finsupp.prod
      rw [map_prod]
      simp only [map_pow, hmapφ]
    rw [hmap, MvPowerSeries.coeff_map]
    exact ⟨_, rfl⟩
  have hOrd : Crude.OrdGe (DF Dw a) f := by
    rw [hfprod, ← hdeg]
    exact ordGe_prod_lemma T φ hφ0 α
  have hPdeg : ∀ m ∈ (P1 Dw T a hn).support, m.degree = DF Dw a := fun m hm =>
    Crude.Pmin_degree (ha := ha) (m := m) (hm := hm)
  refine ⟨f, hfint, hOrd, ?_⟩
  rw [Crude.nabValN_eq_lin B h hg w0 k f (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => uvec ⟨ℓ.1, ℓ.2.1⟩)
    (P1 Dw T a hn) (DF Dw a) hPdeg hOrd, Finset.sum_eq_single α]
  · rw [hfdef, Crude.linMon_aeval_monomial _ _ φ hφ0 _ hdual α α
      (fun l hl => Crude.Pmin_good (m := α) (hm := hαmem) (ℓ := l) (hℓ := hl)), if_pos rfl, hcoeff, one_mul]
    rfl
  · intro m hm hne
    rw [hfdef, Crude.linMon_aeval_monomial _ _ φ hφ0 _ hdual m α
      (fun l hl => Crude.Pmin_good (m := m) (hm := hm) (ℓ := l) (hℓ := hl)), if_neg hne, mul_zero]
  · intro hα
    exact absurd hαmem hα

theorem crude_inf {T : CDVR} {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB T.Fr d O) (h : PS T.Fr 2 d)
    (hg : B.IsCanonGauge T.Fr h) (w0 : O) (k : ℕ) (uvec : Lt1 Dw → Fin d → T.Fr) (hsat : SatDir T uvec)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ha : DomW Dw a) (hn : Fintype.card (Lt1 Dw) ≤ n)
    {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {io : K →+* T.Fr} {e : ℕ}
    (ho : OverLa la T.V io e) :
    crudeInf B h w0 k uvec e a n ≤ (crudeBd la (DF Dw a) : EReal) ∧
      (DF Dw a < resCharOf la → crudeInf B h w0 k uvec e a n ≤ 0) := by
  classical
  obtain ⟨hP, f, hfI, -, hval⟩ := crude_val B h hg w0 k uvec hsat a n ha hn
  have hle : crudeInf B h w0 k uvec e a n ≤ nval T.V e ((fact1 Dw a hn : ℕ) : T.Fr) := by
    unfold crudeInf
    exact iInf_le_of_le (P1 Dw T a hn) (iInf_le_of_le hP (iInf_le_of_le f
      (iInf_le_of_le hfI (by rw [hval]))))
  have hdeg : (Crude.diagExp Dw.mult n (colP Dw hn) (fun τ i => a (τ, i))).degree = DF Dw a := by
    rw [Crude.diagExp_degree]; rfl
  refine ⟨hle.trans ?_, fun hlt => hle.trans ?_⟩
  · have h1 := Crude.nval_factProd_le (ho := ho) (α := Crude.diagExp Dw.mult n (colP Dw hn) (fun τ i => a (τ, i)))
    rw [hdeg] at h1
    exact h1
  · have h2 := Crude.nval_factProd_le_zero (ho := ho) (α := Crude.diagExp Dw.mult n (colP Dw hn) (fun τ i => a (τ, i)))
      (hα := fun s => lt_of_le_of_lt (Crude.le_degree _ s) (hdeg ▸ hlt))
    exact h2

end Gen

end Formalism.L2.Pj
end
end
end
