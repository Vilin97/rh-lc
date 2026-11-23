module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostNormClassCount
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactSetCharPolyCoeffBounded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticPolynomialsBoundedFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCharPolyCoeffBounded
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PAbsSum
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PBaseFrame
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PClsEq
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PClsNorm
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PClsOnto
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PFactorField
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PGenUnit
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PInertBase
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PLocDict
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PLocGood
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PParam
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PQuadField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PStruct
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PTensorCompl
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.RelEquiv
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Mathlib.Tactic.Polynomial.Basic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TwistedTraceFormulaEllipticExpansion
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.UnitPairOfSupport

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.Count1Pf

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

theorem PositivityTheory.Rg.BcB.G3.count1_pf (h1 : Param) : Count1 := by
  intro E _ _ _ hU n S hS P hP y hy hint
  obtain ⟨ι, _, K, L, _, _, _, _, _, _, x, hcard, hR, hC, hA, hsum, ⟨e⟩⟩ :=
    h1 E hU n S hS P hP y hy hint
  rw [Nat.card_congr e, Nat.card_pi, ← hcard, ← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.card_univ,
    ← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => GlobalTheory.QuadSymbol.SignCount.card_classes_mul_two (K i) (L i) (hR i) (hC i) (x i) (hA i)

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.IndexNeZeroOfOpenLe

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.Invar2P

theorem index_ne_zero_of_open_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K U : Subgroup G) (hK : IsCompact (K : Set G)) (hU : IsOpen (U : Set G)) (R : Subgroup K)
    (hR : U.subgroupOf K ≤ R) : R.index ≠ 0 := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen K U hU)
  have h0 : (U.subgroupOf K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  intro h
  apply h0
  exact Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le hR)

end PositivityTheory.Rg.BcB.G3.Invar2P

namespace PositivityTheory.Rg.BcB.G3

theorem invar2_pf : Invar2 := by
  intro E _ _ _ hU a b w K₁ K₂ hK₁ hK₂ φ hφ y g
  obtain ⟨-, -, -, -, hOa, hCa, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU a w
  obtain ⟨-, -, -, -, hOb, hCb, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU b w
  refine GlobalTheory.TwOrbConj.twOrb_twConj _ _ _ y g φ fun x => ?_
  refine Invar2P.index_ne_zero_of_open_le ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) (K₁.prod K₂)
    (by rw [Subgroup.coe_prod]; exact hCa.prod hCb) (by rw [Subgroup.coe_prod]; exact hK₁.1.prod hK₂.1) _ ?_
  intro k hk
  rw [Subgroup.mem_subgroupOf] at hk
  rw [GlobalTheory.TwOrbConj.mem_rStab]
  intro u
  have hθk : ((thL a w).prodMap (thL b w)) (k : GLw a w × GLw b w) ∈ K₁.prod K₂ :=
    Subgroup.mem_prod.2 ⟨hK₁.2.2 _ (Subgroup.mem_prod.1 hk).1, hK₂.2.2 _ (Subgroup.mem_prod.1 hk).2⟩
  have e : ((x * ((u * k : _) : GLw a w × GLw b w))⁻¹ * y * ((thL a w).prodMap (thL b w)) (x * ((u * k : _) : GLw a w × GLw b w))) =
      (k : GLw a w × GLw b w)⁻¹ * ((x * (u : GLw a w × GLw b w))⁻¹ * y * ((thL a w).prodMap (thL b w)) (x * (u : GLw a w × GLw b w))) *
        ((thL a w).prodMap (thL b w)) (k : GLw a w × GLw b w) := by
    simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev]; group
  show φ _ = φ _
  rw [e, (hφ.2 _ hθk _).2, (hφ.2 _ ((K₁.prod K₂).inv_mem hk) _).1]

end PositivityTheory.Rg.BcB.G3
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.IsLevelKGL

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.FinPol2P

theorem isLevel_KGL {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E) :
    IsLevel (thL n w) (GlobalTheory.LFun.KGL w (n := n)) (GlobalTheory.LFun.KGL w (n := n)) :=
  ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1, le_rfl, fun k hk => GlobalTheory.BCT.ThBasic.thL_mem_KGL hU n w k hk⟩

end PositivityTheory.Rg.BcB.G3.FinPol2P

open PositivityTheory.Rg.BcB.G3.FinPol2P in
theorem PositivityTheory.Rg.BcB.G3.finPol2_pf : FinPol2 := by
  intro E _ _ _ hU a b S hS φ hφc hφ1
  have hC₁ : ∀ w, IsCompact (Prod.fst '' tsupport (φ w)) := fun w => (hφc w).image continuous_fst
  have hC₂ : ∀ w, IsCompact (Prod.snd '' tsupport (φ w)) := fun w => (hφc w).image continuous_snd
  choose γ₁ hγ₁0 hγ₁ using fun w => GlobalTheory.LocBound.bound_charpoly_nrmL E a w _ (hC₁ w)
  choose γ₂ hγ₂0 hγ₂ using fun w => GlobalTheory.LocBound.bound_charpoly_nrmL E b w _ (hC₂ w)
  let good : Pl E → Prop := fun w => φ w = (((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) : Subgroup _) :
    Set (GLw a w × GLw b w)).indicator 1
  let g₁ : Pl E → WithZero (Multiplicative ℤ) := fun w => if good w then 1 else γ₁ w
  let g₂ : Pl E → WithZero (Multiplicative ℤ) := fun w => if good w then 1 else γ₂ w
  have hfin₁ := GlobalTheory.BCT.GeoFin.finite_ell_bounded E a S hS g₁
    (fun w => by by_cases h : good w <;> simp [g₁, h, hγ₁0]) (hφ1.mono fun w h => by simp [g₁, good, h])
  have hfin₂ := GlobalTheory.BCT.GeoFin.finite_ell_bounded E b S hS g₂
    (fun w => by by_cases h : good w <;> simp [g₂, h, hγ₂0]) (hφ1.mono fun w h => by simp [g₂, good, h])
  refine (hfin₁.prod hfin₂).subset ?_
  rintro p ⟨h₁, h₂, hp⟩
  have key : ∀ w ∈ S, ((∀ i, Valued.v ((atPl w p.1).coeff i) ≤ g₁ w) ∧ (g₁ w)⁻¹ ≤ Valued.v ((atPl w p.1).coeff 0)) ∧
      ((∀ i, Valued.v ((atPl w p.2).coeff i) ≤ g₂ w) ∧ (g₂ w)⁻¹ ≤ Valued.v ((atPl w p.2).coeff 0)) := by
    intro w hw
    obtain ⟨y, hy, e₁, e₂⟩ := hp w hw
    rw [← e₁, ← e₂]
    by_cases hg : good w
    · simp only [g₁, g₂, if_pos hg, inv_one]
      have hy' : y ∈ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) := by
        have hy2 := hy
        rw [show φ w = _ from hg] at hy2
        by_contra hc
        exact hy2 (Set.indicator_of_notMem hc _)
      exact ⟨GlobalTheory.BCT.GeoFin.charpoly_nrmL_integral E a w (isLevel_KGL hU a w) y.1 hy'.1,
        GlobalTheory.BCT.GeoFin.charpoly_nrmL_integral E b w (isLevel_KGL hU b w) y.2 hy'.2⟩
    · simp only [g₁, g₂, if_neg hg]
      have hyt : y ∈ tsupport (φ w) := subset_tsupport _ hy
      exact ⟨hγ₁ w y.1 ⟨y, hyt, rfl⟩, hγ₂ w y.2 ⟨y, hyt, rfl⟩⟩
  exact ⟨⟨h₁, fun w hw => (key w hw).1⟩, ⟨h₂, fun w hw => (key w hw).2⟩⟩

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PSkewEx

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3

theorem skewEx_pf : SkewEx := by
  intro E _ _ _
  obtain ⟨x, hx⟩ : ∃ x : E, IsCMField.complexConj E x ≠ x := by
    by_contra h
    push Not at h
    exact IsCMField.complexConj_ne_one (K := E) (AlgEquiv.ext h)
  have hconj : IsCMField.complexConj E (x - IsCMField.complexConj E x) = -(x - IsCMField.complexConj E x) := by
    rw [map_sub, IsCMField.complexConj_apply_apply, neg_sub]
  have hmem : (x - IsCMField.complexConj E x) ^ 2 ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_pow, hconj, neg_sq]
  exact ⟨x - IsCMField.complexConj E x, ⟨_, hmem⟩, sub_ne_zero.mpr (Ne.symm hx), hconj, rfl⟩

end PositivityTheory.Rg.BcB.G3

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PSplitSq

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3

theorem splitSq_pf (h1 : TensorCompl) : SplitSq := by
  intro E _ _ _ s d hs hcs hd w hw
  have hcm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom :=
    ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
      fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩
  obtain ⟨u, hne, hu⟩ := hw
  have hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 (maximalRealSubfield E))) :=
    ⟨u, w, hne, congrArg HeightOneSpectrum.asIdeal hu, rfl⟩
  obtain ⟨τ, -⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq hcm hv rfl
  refine ⟨τ s, ?_⟩
  have key : τ (algebraMap (maximalRealSubfield E) E d) = τ s * τ s := by rw [hd, pow_two, map_mul]
  exact (τ.commutes d).symm.trans key

end PositivityTheory.Rg.BcB.G3

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.SuppPf

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.SuppP
end PositivityTheory.Rg.BcB.G3.SuppP

theorem PositivityTheory.Rg.BcB.G3.supp_pf : PositivityTheory.Rg.BcB.G3.Supp := by
  intro G _ _ θ K y f h
  by_contra hne
  push Not at hne
  apply h
  unfold twOrb avg
  simp only [hne, finsum_zero, mul_zero]
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TwConjOfMkEq

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.FinCl2P

theorem rel_of_eqvGen {G : Type} [Group G] (θ : G →* G) {x y : G}
    (h : Relation.EqvGen (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) x y) : ∃ g, y = g⁻¹ * x * θ g := by
  induction h with
  | rel a b hab => exact hab
  | refl a => exact ⟨1, by simp⟩
  | symm a b _ ih =>
    obtain ⟨g, rfl⟩ := ih
    exact ⟨g⁻¹, by rw [map_inv]; group⟩
  | trans a b c _ _ ih1 ih2 =>
    obtain ⟨g, rfl⟩ := ih1
    obtain ⟨k, rfl⟩ := ih2
    exact ⟨g * k, by rw [map_mul]; group⟩

theorem twConj_of_mk_eq {G : Type} [Group G] {θ : G →* G} {x y : G}
    (h : (Quot.mk _ x : TwCl θ) = Quot.mk _ y) : ∃ g, y = g⁻¹ * x * θ g :=
  rel_of_eqvGen θ (Quot.eqvGen_exact h)

theorem rep_mk {G : Type} [Group G] {θ : G →* G} (y : G) :
    ∃ g, TwCl.rep (Quot.mk _ y : TwCl θ) = g⁻¹ * y * θ g :=
  twConj_of_mk_eq (θ := θ) (Quot.out_eq (Quot.mk _ y : TwCl θ)).symm

theorem charpoly_rep_mk {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (y : GLw n w) : (nrmL n w (TwCl.rep (Quot.mk _ y : TwCl (thL n w)))).val.charpoly = (nrmL n w y).val.charpoly := by
  obtain ⟨g, hg⟩ := rep_mk (θ := thL n w) y
  rw [hg, GlobalTheory.BCT.ThBasic.nrmL_twist hU n w g y, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
    Matrix.charpoly_units_conj']

end PositivityTheory.Rg.BcB.G3.FinCl2P

open PositivityTheory.Rg.BcB.G3.FinCl2P in
theorem PositivityTheory.Rg.BcB.G3.finCl2_pf : FinCl2 := by
  intro E _ _ _ hU a b w Q₁ Q₂ h₁ h₂
  set θ := (thL a w).prodMap (thL b w) with hθ
  let f : TwCl θ → TwCl (thL a w) × TwCl (thL b w) := fun l => (Quot.mk _ l.rep.1, Quot.mk _ l.rep.2)
  have hinj : Function.Injective f := by
    intro l l' hll'
    obtain ⟨g₁, hg₁⟩ := twConj_of_mk_eq (congrArg Prod.fst hll')
    obtain ⟨g₂, hg₂⟩ := twConj_of_mk_eq (congrArg Prod.snd hll')
    have hq : (Quot.mk _ l.rep : TwCl θ) = Quot.mk _ l'.rep :=
      Quot.sound ⟨(g₁, g₂), Prod.ext (by simpa [hθ] using hg₁) (by simpa [hθ] using hg₂)⟩
    have e1 : (Quot.mk _ l.rep : TwCl θ) = l := Quot.out_eq l
    have e2 : (Quot.mk _ l'.rep : TwCl θ) = l' := Quot.out_eq l'
    rw [← e1, ← e2, hq]
  have hA := (GlobalTheory.BCT.ClsFin.classes_finite E hU a w Q₁ h₁).1
  have hB := (GlobalTheory.BCT.ClsFin.classes_finite E hU b w Q₂ h₂).1
  refine ((hA.prod hB).preimage hinj.injOn).subset ?_
  rintro l ⟨hl₁, hl₂⟩
  refine ⟨?_, ?_⟩
  · change (nrmL a w (TwCl.rep (Quot.mk _ l.rep.1 : TwCl (thL a w)))).val.charpoly = Q₁
    rw [charpoly_rep_mk hU a w, hl₁]
  · change (nrmL b w (TwCl.rep (Quot.mk _ l.rep.2 : TwCl (thL b w)))).val.charpoly = Q₂
    rw [charpoly_rep_mk hU b w, hl₂]
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.Count1

section

@[expose] public section

namespace PositivityTheory.Rg.BcB.G3

theorem param : Param :=
  param_pf skewEx_pf (struct_pf factorField_pf) quadField_pf
    (locDict_pf clsNorm_pf clsOnto_pf clsEq_pf baseFrame_pf (inertBase_pf tensorCompl_pf) (splitSq_pf tensorCompl_pf)
      tensorCompl_pf) clsNorm_pf clsOnto_pf clsEq_pf locGood_pf

theorem count1 : Count1 := count1_pf param

theorem g3 : G8.G3 :=
  twisted_trace_formula_elliptic_expansion absSum_pf finCl2_pf invar2_pf (unit_pair_of_support locGood_pf genUnit_pf supp_pf) (count2_pf count1) supp_pf finPol2_pf

end PositivityTheory.Rg.BcB.G3
end
end
