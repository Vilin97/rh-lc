module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.ExtraTr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Formalism.SharpRestriction.GlobalTheoremInputs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParametersFamilyConstStatement
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.OptInEqSome
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeLocus
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.LengthLeOfSpan
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Sheaves.Presheaf

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.EvPowLeExp

section

@[expose] public section

noncomputable section

namespace UpperTheory.GalC

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField

theorem lw_ram_nonneg (D : D7) (w : D.what₂.places.Pl) : 0 ≤ SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) := by
  refine mul_nonneg ?_ (Nat.cast_nonneg _)
  unfold SizeData₂.lwP lw
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

open Classical in
theorem sum_val_le {D : D7} (L : SizeData₂ D) (N : ℕ) (hN : N ≠ 0) :
    ∑ w ∈ L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0),
      SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * (padicValNat (D.what₂.places.resChar w) N : ℝ) ≤ Real.log N := by
  have h1 : Real.log N = ∑ l ∈ N.primeFactors, (padicValNat l N : ℝ) * Real.log l := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hl), Nat.padicValNat_def]
  rw [h1, ← Finset.sum_filter_add_sum_filter_not _ (fun w => D.what₂.places.resChar w ∈ N.primeFactors)]
  have h0 : ∑ w ∈ (L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0)).filter
      (fun w => ¬ D.what₂.places.resChar w ∈ N.primeFactors),
      SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * (padicValNat (D.what₂.places.resChar w) N : ℝ) = 0 := by
    refine Finset.sum_eq_zero fun w hw => ?_
    have h2 := (Finset.mem_filter.1 hw).2
    have h3 : ¬ D.what₂.places.resChar w ∣ N := fun h =>
      h2 (Nat.mem_primeFactors.2 ⟨D.what₂.places.resChar_prime w, h, hN⟩)
    rw [Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd h3]; simp
  rw [h0, add_zero, ← Finset.sum_fiberwise_of_maps_to (g := fun w => D.what₂.places.resChar w) (t := N.primeFactors)
    (fun w hw => (Finset.mem_filter.1 hw).2)]
  refine Finset.sum_le_sum fun l hl => ?_
  have hm := TwistedPlaces.admissibleMeanCondition_holds L l (Nat.prime_of_mem_primeFactors hl)
  calc _ = (padicValNat l N : ℝ) * ∑ w ∈ TwistedPlaces.twAt L l, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr ?_ fun w hw => ?_
        · ext w
          simp only [Finset.mem_filter, TwistedPlaces.mem_twAt, TwistedPlaces.TwPl]
          constructor
          · rintro ⟨⟨⟨a, b⟩, -⟩, e⟩; exact ⟨a, b, e⟩
          · rintro ⟨a, b, e⟩; exact ⟨⟨⟨a, b⟩, e ▸ hl⟩, e⟩
        · rw [(TwistedPlaces.mem_twAt.1 hw).2.2]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)

open Classical in
theorem etaSum_le_add {D : D7} (L : SizeData₂ D) (j : ℕ) (η : D.what₂.places.Pl → ℝ) (d : ℝ) (hd : 0 ≤ d) (N : ℕ) (hN : N ≠ 0)
    (h : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
      (D.what₂.etaJ j w : ℝ) ≤ η w + d * (padicValNat (D.what₂.places.resChar w) N : ℝ)) :
    Formalism.MainNotions.etaSum L j ≤ (∑ w ∈ L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0),
      SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * η w) + d * Real.log N := by
  refine le_trans ?_ (add_le_add_right (mul_le_mul_of_nonneg_left (sum_val_le L N hN) hd) _)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun w hw => ?_
  have := mul_le_mul_of_nonneg_left (h w (Finset.mem_filter.1 hw).2) (lw_ram_nonneg D w)
  linarith

theorem ev_pow_le_exp (C eps : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ x ≥ x0, x ^ C ≤ Real.exp (x ^ eps) ∧ 1 ≤ x ^ eps := by
  have h2 := ((isLittleO_log_rpow_atTop he).const_mul_left C).bound one_pos
  obtain ⟨x0, h⟩ := Filter.eventually_atTop.1 (h2.and (Filter.eventually_ge_atTop 1))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨a, b⟩ := h x hx
  have x0' : 0 < x := by linarith
  refine ⟨?_, Real.one_le_rpow b he.le⟩
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg x0'.le _), Real.norm_eq_abs] at a
  rw [Real.rpow_def_of_pos x0', mul_comm]
  exact Real.exp_le_exp.2 ((le_abs_self _).trans a)

end UpperTheory.GalC
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.IsHeckeGaloisIff

section

@[expose] public section

noncomputable section

namespace UpperTheory.GalC

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.HeightCounting Alg TensorProduct

variable {D : D7} {c : CutD D}

theorem mem_Zgood {i : (cut D c).nd.Loc} {x : (cut D c).nd.X i} : x ∈ (cut D c).nd.Zgood i ↔ x.1 ∈ D.nd.Zgood i.1 := by
  classical
  exact Finset.mem_subtype

theorem eta_le (h : c.Good) (i : (cut D c).nd.Loc) : D.nd.etaLoc i.1 ≤ (cut D c).nd.etaLoc i +
    (∑ x ∈ D.nd.Zgood i.1, D.nd.mult i.1 x : ℕ) * (padicValNat (D.nd.l i.1) D.what₂.restRowsFiniteGroupCard : ℚ) := by
  classical
  obtain ⟨α, -, hα1, hα2⟩ := h.op i.1 i.2
  have hn : D.what₂.restRowsFiniteGroupCard ≠ 0 := (D.what₂.restRowsFiniteGroupCard_pos).ne'
  have hA : ((D.what₂.restRowsFiniteGroupCard : ℕ) : D.nd.O i.1) ≠ 0 := by
    intro hz
    have h1 : ((D.what₂.restRowsFiniteGroupCard : D.what₂.LL) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have h2 : D.nd.embK i.1 (D.what₂.restRowsFiniteGroupCard : D.what₂.LL) = 0 := by
      rw [map_natCast, ← map_natCast (algebraMap (D.nd.O i.1) (FractionRing (D.nd.O i.1))), hz, map_zero]
    exact h1 ((map_eq_zero_iff _ (D.nd.embK i.1).injective).mp h2)
  have hα1' : ∀ x ∈ D.nd.Zgood i.1, ∀ u ∈ heckeEig (D.nd.T i.1) (D.nd.act i.1) x,
      (LinearMap.baseChange (FractionRing (D.nd.O i.1)) α) u = ((D.what₂.restRowsFiniteGroupCard : ℕ) : D.nd.O i.1) • u := by
    intro x hx u hu
    rw [hα1 x hx u hu, Int.cast_natCast, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  have hY : ∀ x : ↥(c.Xs i.1), x ∈ (((cut D c).nd.Zgood i : Finset ((cut D c).nd.X i)) : Set ((cut D c).nd.X i)) ↔
      (x : D.nd.X i.1) ∈ D.nd.Zgood i.1 :=
    fun x => Iff.trans Finset.mem_coe mem_Zgood
  have key := Alg.length_le (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (D.nd.T_sep i.1) (D.nd.Zgood i.1) _ hY α _ hA hα1' hα2
  have hfinE : Module.length (D.nd.O i.1) (D.nd.O i.1 ⧸ Ideal.span {((D.what₂.restRowsFiniteGroupCard : ℕ) : D.nd.O i.1)}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_of_ne_zero hA))
  have hpad := GlobalTheory.CutAtGood.lenUnit_natCast_le i.1 D.what₂.restRowsFiniteGroupCard hn
  refine (Alg.lenUnit_le_add (D.nd.l i.1) _ hfinE (fun hC => absurd hC ?_) key).trans ?_
  · exact Alg.length_ne_top ((cut D c).nd.T i) ((cut D c).nd.act i) ((cut D c).nd.T_sep i) ((cut D c).nd.Zgood i)
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hpad (Nat.cast_nonneg _))

theorem eta_zero {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (h : N.Zgood i = ∅) :
    N.etaLoc i = 0 := by
  have hsum : N.eigSum i ↑(N.Zgood i) = ⊥ := by
    rw [h]
    simp [NData.eigSum]
  have hup : N.MtUp i = ⊥ := by
    simp [NData.MtUp, hsum]
  have hsub : Subsingleton (N.MtUp i) := by
    rw [hup]
    infer_instance
  have hq : Subsingleton (↥(N.MtUp i) ⧸ Submodule.comap (N.MtUp i).subtype (N.MtLow i)) := by
    infer_instance
  unfold NData.etaLoc lenUnit
  rw [Module.length_eq_zero]
  simp

theorem etaJ_le (h : c.Good) (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    (D.what₂.etaJ j w : ℝ) ≤ ((cut D c).what₂.etaJ j w : ℝ) +
      (∑ i ∈ D.nd.locs j w, ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ)) *
        (padicValNat (D.what₂.places.resChar w) D.what₂.restRowsFiniteGroupCard : ℝ) := by
  classical
  let F : D.nd.Loc → ℚ := fun i => if hk : c.keep i then (cut D c).nd.etaLoc (⟨i, hk⟩ : (cut D c).nd.Loc) else 0
  have hcut : (cut D c).what₂.etaJ j w = ∑ i ∈ D.nd.locs j w, F i := by
    rw [(cut D c).etaJ_tie j w h1 h2]
    show ∑ i ∈ Finset.subtype c.keep (D.nd.locs j w), (cut D c).nd.etaLoc i = _
    have hF : ∀ i ∈ Finset.subtype c.keep (D.nd.locs j w), (cut D c).nd.etaLoc i = F i.1 := by
      intro i _
      simp only [F, dif_pos i.2]
    rw [Finset.sum_congr rfl hF, Finset.sum_subtype_eq_sum_filter]
    refine Finset.sum_filter_of_ne ?_
    intro i _ hne
    by_contra hk
    exact hne (dif_neg hk)
  have hD := D.etaJ_tie j w h1 h2
  have hpt : ∀ i ∈ D.nd.locs j w, D.nd.etaLoc i ≤ F i +
      (∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℚ)) * (padicValNat (D.what₂.places.resChar w) D.what₂.restRowsFiniteGroupCard : ℚ) := by
    intro i hi
    have hw : D.nd.w i = w := ((D.nd.locs_mem j w i).mp hi).2
    have hl : D.what₂.places.resChar w = D.nd.l i := by
      rw [← hw]
      exact D.nd.w_l i
    rw [hl]
    by_cases hk : c.keep i
    · have hb := eta_le h (⟨i, hk⟩ : (cut D c).nd.Loc)
      simp only [F, dif_pos hk]
      push_cast at hb
      exact hb
    · have hz : D.nd.Zgood i = ∅ := by
        rw [← Finset.not_nonempty_iff_eq_empty]
        exact fun hne => hk ((h.keep i).mpr hne)
      rw [eta_zero D.nd i hz]
      simp only [F, dif_neg hk, zero_add]
      positivity
  have hQ : D.what₂.etaJ j w ≤ (cut D c).what₂.etaJ j w +
      (∑ i ∈ D.nd.locs j w, ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℚ)) *
        (padicValNat (D.what₂.places.resChar w) D.what₂.restRowsFiniteGroupCard : ℚ) := by
    rw [hD, hcut, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hpt
  exact_mod_cast hQ

end UpperTheory.GalC
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.LinkNOfGd

section

@[expose] public section

noncomputable section

namespace UpperTheory.GalC

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField

variable {eps : ℝ}



def gd (Fm : FamP eps) (c : ∀ x (i : Fm.Ix x), CutD (Fm.D x i)) : FamP eps :=
  { Fm with
    D := fun x i => (raw (c x i)).rec'
    L := fun x i => Gen.ledTr (raw (c x i)) (Fm.L x i)
    params := fun x hx i => Gen.parTr (raw (c x i)) (Fm.params x hx i)
    parT := fun x hx i => Gen.parTTr (raw (c x i)) (Fm.parT x hx i)
    ties := fun x i => tiesTr (c x i) (Fm.ties x i)
    gatT := fun x i => Gen.gatTr (raw (c x i)) (Fm.gatT x i)
    X := fun x i => Gen.divTr (raw (c x i)) (Fm.X x i)
    Gx := fun x i => Gen.instTr (raw (c x i)) (Fm.Gx x i)
    Gy := fun x i => Gen.latTr (raw (c x i)) (Fm.Gy x i)
    fills := fun x hx i w => Gen.fills_tr (raw (c x i)) _ _ w (Fm.fills x hx i w)
    rrDef := fun x hx i => Gen.rrDefTr (raw (c x i)) (Fm.rrDef x hx i)
    ex := fun x hx i => extraTr (c x i) (Fm.ex x hx i) }

theorem twGood_gd (Fm : FamP eps) (c : ∀ x (i : Fm.Ix x), CutD (Fm.D x i)) (h : TwGood Fm) : TwGood (gd Fm c) := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx0 hx i => twAt_tr (c x i) (h x hx0 hx i)⟩


open Classical in
theorem linkN_of_gd (Fm : FamP eps) (c : ∀ x (i : Fm.Ix x), CutD (Fm.D x i))
    (hc : ∀ x, Fm.x1 < x → ∀ i, (c x i).Good ∧ GlobalTheory.NLink.MultLe (Fm.L x i) ∧ TwistedPlaces.adm3 (Fm.L x i))
    (h : LinkN (gd Fm c)) : LinkN Fm := by
  obtain ⟨C, x0, h⟩ := h
  obtain ⟨C1, x1, hC1, hpar⟩ := GlobalTheory.T.admissible_parameters_family_const Fm
  obtain ⟨i0⟩ := Fm.Ix_zero
  have he : 0 < eps := Fm.L_eps 0 i0 ▸ (Fm.L 0 i0).sc.eps_pos
  obtain ⟨x2, hev⟩ := ev_pow_le_exp C1 eps he
  refine ⟨C + C1, max (max x0 x1) (max x2 (Fm.x1 + 1)), fun x hx i hS j hj hsum => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hx
  obtain ⟨⟨a0, a1⟩, a2, a3⟩ := hx
  have hx1 : Fm.x1 < x := by linarith
  obtain ⟨hg, hm, h3⟩ := hc x hx1 i
  have k := h x a0 i hS j hj hsum
  have hj' : 1 ≤ j ∧ j ≤ (Fm.D x i).R.m := Finset.mem_Icc.1 hj
  have hN : (Fm.D x i).what₂.restRowsFiniteGroupCard ≠ 0 := (Fm.D x i).what₂.restRowsFiniteGroupCard_pos.ne'
  have e := etaSum_le_add (Fm.L x i) j (fun w => ((cut (Fm.D x i) (c x i)).what₂.etaJ j w : ℝ)) ((Fm.L x i).dZ0 j)
    (Nat.cast_nonneg _) _ hN fun w hw => by
      refine (etaJ_le hg j w hj'.1 hj'.2).trans (add_le_add_right (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)) _)
      have := hm j hj w hw
      rwa [h3 j hj w hw] at this
  have hlog : Real.log ((Fm.D x i).what₂.restRowsFiniteGroupCard : ℝ) ≤ C1 * (Fm.L x i).sc.x ^ C1 * (Fm.L x i).sc.L :=
    (hpar x a1 hx1 i).2.2.2.2.2.2.2
  have ex : (Fm.L x i).sc.x = x := Fm.L_x x i (by linarith [Fm.one_lt_family_threshold])
  have ee : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hL : 1 ≤ (Fm.L x i).sc.L := by rw [Scale.L, ex, ee]; exact (hev x a2).2
  have hb : (Fm.L x i).sc.x ^ C1 ≤ (Fm.L x i).sc.b := by rw [Scale.b, Scale.L, ex, ee]; exact (hev x a2).1
  have hm1 : (1 : ℝ) ≤ (Fm.D x i).R.m := by exact_mod_cast hj'.1.trans hj'.2
  have hf1 : (1 : ℝ) ≤ (Fm.D x i).R.f := by
    have : (Fm.D x i).R.m ≤ (Fm.D x i).R.f := (Fm.D x i).R.m_le_f
    exact hm1.trans (by exact_mod_cast this)
  have hb0 : 0 ≤ (Fm.L x i).sc.b := (Real.exp_pos _).le
  have hNc : 0 ≤ Real.log (Fm.L x i).sc.x ^ 2 * ((Fm.L x i).Nc : ℝ) := mul_nonneg (sq_nonneg _) (by
    have := (Fm.L x i).sc.one_lt_alt
    have x0 : 0 < (Fm.L x i).sc.x := by linarith
    unfold SizeData₂.Nc budgetNc rankBudget bSize
    positivity)
  have t1 : (Fm.L x i).sc.x ^ C1 * (Fm.L x i).sc.L ≤
      ((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b * (Fm.L x i).sc.L ^ 2 := by
    have u1 : (1 : ℝ) ≤ ((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.m := one_le_mul_of_one_le_of_one_le hf1 hm1
    have u2 : (Fm.L x i).sc.L ≤ (Fm.L x i).sc.L ^ 2 := by nlinarith
    calc _ ≤ (Fm.L x i).sc.b * (Fm.L x i).sc.L ^ 2 := mul_le_mul hb u2 (by linarith) hb0
      _ = 1 * ((Fm.L x i).sc.b * (Fm.L x i).sc.L ^ 2) := (one_mul _).symm
      _ ≤ _ := by rw [mul_assoc (_ * _)]; exact mul_le_mul_of_nonneg_right u1 (by positivity)
  have t2 : Real.log ((Fm.D x i).what₂.restRowsFiniteGroupCard : ℝ) ≤ C1 * (((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b *
      (Fm.L x i).sc.L ^ 2 + Real.log (Fm.L x i).sc.x ^ 2 * ((Fm.L x i).Nc : ℝ)) := by
    rw [mul_assoc] at hlog
    exact hlog.trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
  have k' : (∑ w ∈ (Fm.L x i).supp.filter (fun w => (Fm.D x i).what₂.muAt w ≠ (Fm.D x i).what₂.mu0),
      SizeData₂.lwP w * ((Fm.D x i).what₂.places.ramIdx w : ℝ) * ((cut (Fm.D x i) (c x i)).what₂.etaJ j w : ℝ)) ≤
      ((Fm.L x i).dZ0 j : ℝ) * (C * (((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b * (Fm.L x i).sc.L ^ 2 +
        Real.log (Fm.L x i).sc.x ^ 2 * ((Fm.L x i).Nc : ℝ)) + ∑' l, vvTerm (Fm.D x i) l) := k
  have t3 := mul_le_mul_of_nonneg_left t2 (Nat.cast_nonneg (α := ℝ) ((Fm.L x i).dZ0 j))
  refine e.trans ?_
  calc _ ≤ _ := add_le_add k' t3
    _ = _ := by ring

end UpperTheory.GalC
end
end
end
