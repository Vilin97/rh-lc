module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Clause3Asc
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.RestrictAtPointHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.AscSeedOfLocSub
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ExistsProj2
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.LsProps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.IsLocCompTwistFills
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete

-- Source module: Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.FrobRecipHolds

section

@[expose] public section

noncomputable section

open GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.PRep

namespace PositivityTheory.Rg.Rs

namespace SliceFrobeniusReciprocity

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N c : ℕ} {n : Fin c → ℕ} {h : ∑ i, n i = N} {σ' : SmIrr (GL (Fin N) k)} {W : Type} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (∀ i, GL (Fin (n i)) k) W} {ℓ : σ'.V →ₗ[ℂ] W}

def frobFun (hℓ : ∀ (p : parab k (stdBlocks n h)) (v : σ'.V),
      ℓ (σ'.ρ p v) = ρ (leviProj k (stdBlocks n h) p) (ℓ v)) (v : σ'.V) :
    IndSp (stdBlocks n h) (twist ρ (deltaHalf k fun i => Fin (n i))⁻¹) :=
  ⟨⟨fun g => ℓ (σ'.ρ g v), fun p g => by
      show ℓ (σ'.ρ ((p : GL (Fin N) k) * g) v) = _
      rw [map_mul, Module.End.mul_apply, hℓ p]
      simp only [MonoidHom.coe_comp, Function.comp_apply, twist_apply, smul_smul, ← Units.val_mul,
        MonoidHom.inv_apply, mul_inv_cancel, Units.val_one, one_smul]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset ((σ'.smooth v).mem_nhds (by simp)) fun g hg => by
      have hg' : σ'.ρ g v = v := hg
      show _ = _
      apply Subtype.ext
      funext x
      show ℓ (σ'.ρ (x * g) v) = ℓ (σ'.ρ x v)
      rw [map_mul, Module.End.mul_apply, hg'])⟩

theorem frobFun_apply (hℓ : ∀ (p : parab k (stdBlocks n h)) (v : σ'.V),
      ℓ (σ'.ρ p v) = ρ (leviProj k (stdBlocks n h) p) (ℓ v)) (v : σ'.V) (g : GL (Fin N) k) :
    (frobFun hℓ v).1.1 g = ℓ (σ'.ρ g v) := rfl

def frobMap (hℓ : ∀ (p : parab k (stdBlocks n h)) (v : σ'.V),
      ℓ (σ'.ρ p v) = ρ (leviProj k (stdBlocks n h) p) (ℓ v)) :
    σ'.ρ.IntertwiningMap (parInd (stdBlocks n h) (twist ρ (deltaHalf k fun i => Fin (n i))⁻¹)) where
  toLinearMap :=
    { toFun := frobFun hℓ
      map_add' := fun v v' => Subtype.ext (Subtype.ext (funext fun g => by
        show ℓ (σ'.ρ g (v + v')) = ℓ (σ'.ρ g v) + ℓ (σ'.ρ g v')
        simp))
      map_smul' := fun a v => Subtype.ext (Subtype.ext (funext fun g => by
        show ℓ (σ'.ρ g (a • v)) = a • ℓ (σ'.ρ g v)
        simp)) }
  isIntertwining' g := by
    ext v x
    show ℓ (σ'.ρ x (σ'.ρ g v)) = ℓ (σ'.ρ (x * g) v)
    rw [map_mul, Module.End.mul_apply]

end SliceFrobeniusReciprocity

open SliceFrobeniusReciprocity in
theorem frobRecip_holds : PositivityTheory.RSHS.LS.FrobRecip := by
  intro k _ _ _ _ N c n h σ' W _ _ ρ ℓ hℓ0 hℓ
  refine ⟨frobMap hℓ, fun h0 => hℓ0 (LinearMap.ext fun v => ?_)⟩
  have h1 := congrArg (fun f : _ →ₗ[ℂ] _ => (f v).1.1 1) h0
  simpa [frobMap, frobFun_apply] using h1

end PositivityTheory.Rg.Rs

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.PiTensorTwistTprod

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.RSHS.LocalComponentTwist

theorem modExp_const {a d : ℕ} (i : Fin d) :
    modExp (fun _ : Fin d => Fin a) i = (a : ℤ) * ((d : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)) := by
  have e : modExp (fun _ : Fin d => Fin a) i =
      (∑ _b ∈ Finset.Ioi i, (a : ℤ)) - ∑ _b ∈ Finset.Iio i, (a : ℤ) := by
    unfold modExp
    congr 1
    · exact Finset.sum_congr (by ext; simp) fun _ _ => by simp
    · exact Finset.sum_congr (by ext; simp) fun _ _ => by simp
  have hi := i.2
  have hc : ((d - 1 - (i : ℕ) : ℕ) : ℤ) = (d : ℤ) - 1 - ((i : ℕ) : ℤ) := by omega
  rw [e, Finset.sum_const, Finset.sum_const, Fin.card_Ioi, Fin.card_Iio, nsmul_eq_mul, nsmul_eq_mul, hc]
  ring

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a d : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem piTensor_twist_tprod (ρ : Representation ℂ (GL (Fin a) k) V) (χ : Fin d → GL (Fin a) k →* ℂˣ)
    (g : Fin d → GL (Fin a) k) (x : Fin d → V) :
    piTensor (fun i => GlobalTheory.SmGL.twist ρ (χ i)) g (PiTensorProduct.tprod ℂ x) =
      ((∏ i, χ i (g i) : ℂˣ) : ℂ) • PiTensorProduct.tprod ℂ fun i => ρ (g i) (x i) := by
  rw [piTensor_tprod, Units.coe_prod]
  exact (PiTensorProduct.tprod ℂ).map_smul_univ (fun i => ((χ i (g i) : ℂˣ) : ℂ)) fun i => ρ (g i) (x i)

theorem levi_eq (ρ : Representation ℂ (GL (Fin a) k) V) (s t : Fin d → ℂ)
    (hst : ∀ i, t i = ((modExp (fun _ : Fin d => Fin a) i : ℤ) : ℂ) / 2 + s i) :
    piTensor (fun i => GlobalTheory.SmGL.twist ρ (detChar (Fin a) (absPow k (s i)))) =
      GlobalTheory.SmGL.twist (piTensor fun i => GlobalTheory.SmGL.twist ρ (detChar (Fin a) (absPow k (t i))))
        (deltaHalf k fun _ : Fin d => Fin a)⁻¹ := by
  refine MonoidHom.ext fun g => ?_
  have key : (deltaHalf k fun _ : Fin d => Fin a)⁻¹ g * ∏ i, detChar (Fin a) (absPow k (t i)) (g i) =
      ∏ i, detChar (Fin a) (absPow k (s i)) (g i) := by
    rw [MonoidHom.inv_apply, deltaHalf_apply, inv_mul_eq_iff_eq_mul, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [detChar_apply, detChar_apply, hst i, absPow_add, MonoidHom.mul_apply]
  refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply, GlobalTheory.SmGL.twist_apply,
    piTensor_twist_tprod, piTensor_twist_tprod, smul_smul, ← Units.val_mul, key]

theorem levi_equiv (ρ : Representation ℂ (GL (Fin a) k) V) (s t : Fin d → ℂ)
    (hst : ∀ i, t i = ((modExp (fun _ : Fin d => Fin a) i : ℤ) : ℂ) / 2 + s i)
    (ψ : Fin d → GL (Fin a) k →* ℂˣ) (hψ : ∀ i, ψ i = detChar (Fin a) (absPow k (t i))) :
    Nonempty ((piTensor fun i => GlobalTheory.SmGL.twist ρ (detChar (Fin a) (absPow k (s i)))).Equiv
      (GlobalTheory.SmGL.twist (piTensor fun i => GlobalTheory.SmGL.twist ρ (ψ i)) (deltaHalf k fun _ : Fin d => Fin a)⁻¹)) := by
  obtain rfl : ψ = fun i => detChar (Fin a) (absPow k (t i)) := funext hψ
  exact ⟨.mk (.refl ℂ _) fun g => by
    rw [levi_eq ρ s t hst]
    rfl⟩

end Local

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem loc_eq_absPow {ν : HChar E} {s : ℝ} (hν : ν.IsAbsPow s) (w : HeightOneSpectrum (𝓞 E)) :
    ν.loc w = GlobalTheory.SmGL.absPow (w.adicCompletion E) s := by
  ext x
  have hgeneral {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k] (x : kˣ) :
      GlobalTheory.SplitWeil.nabs k x = (GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-GlobalTheory.SmGL.ord k x) := by
    open ValuativeRel in
    have hpow (x : kˣ) (m : ℕ) : GlobalTheory.SmGL.ord k (x ^ m) = m * GlobalTheory.SmGL.ord k x := by
      induction m with
      | zero =>
        simp only [pow_zero, Nat.cast_zero, zero_mul]
        exact GlobalTheory.SmGL.ord_eq_zero (by simp only [Units.val_one, map_one])
      | succ m ih =>
        rw [pow_succ, GlobalTheory.SmGL.ord_mul, ih]
        push_cast
        ring
    have hexists : ∃ ϖ : kˣ, GlobalTheory.SmGL.ord k ϖ = 1 ∧
        GlobalTheory.SplitWeil.nabs k ϖ = (GlobalTheory.SplitWeil.resCard k : ℝ)⁻¹ := by
      obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (valuation k).integer
      have hp0 : (p : k) ≠ 0 := by
        intro h
        exact hp.ne_zero (Subtype.ext h)
      obtain ⟨y, hy⟩ : ∃ y : k, valuation k y = uniformizer k := valuation_surjective _
      have hy0 : y ≠ 0 := by
        intro h
        rw [h, map_zero] at hy
        exact (uniformizer_pos (R := k)).ne hy
      have hyint : y ∈ (valuation k).integer := by
        rw [Valuation.mem_integer_iff, hy]
        exact uniformizer_lt_one.le
      obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (x := (⟨y, hyint⟩ : (valuation k).integer)) (fun h => hy0 (congrArg Subtype.val h)) hp
      have hu0 : ((u : (valuation k).integer) : k) ≠ 0 := by
        intro h
        exact u.ne_zero (Subtype.ext h)
      refine ⟨Units.mk0 (p : k) hp0, ?_, _root_.GlobalTheory.SplitWeil.nabs_uniformiser hp rfl⟩
      have hyo : _root_.GlobalTheory.SmGL.ord k (Units.mk0 y hy0) = 1 :=
        _root_.GlobalTheory.SmGL.ord_eq_one hy
      have huo : _root_.GlobalTheory.SmGL.ord k (Units.mk0 _ hu0) = 0 := by
        apply _root_.GlobalTheory.SmGL.ord_eq_zero
        exact (Valuation.integer.integers (valuation k)).one_of_isUnit u.isUnit
      have hsplit : Units.mk0 y hy0 = Units.mk0 _ hu0 * Units.mk0 (p : k) hp0 ^ m := by
        ext
        have := congrArg Subtype.val hu
        simpa using this
      rw [hsplit, _root_.GlobalTheory.SmGL.ord_mul, huo, hpow,
        zero_add] at hyo
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hyo with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2
      · omega
    obtain ⟨ϖ, hord, habs⟩ := hexists
    have hq : (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ≠ 0 := by
      have := _root_.GlobalTheory.SplitWeil.one_lt_resCard k
      positivity
    have hinv : _root_.GlobalTheory.SplitWeil.nabs k ϖ⁻¹ = _root_.GlobalTheory.SplitWeil.resCard k := by
      have h := _root_.GlobalTheory.SplitWeil.nabs_mul k ϖ ϖ⁻¹
      rw [mul_inv_cancel, _root_.GlobalTheory.SplitWeil.nabs_one, habs] at h
      exact ((inv_mul_eq_one₀ hq).mp h.symm).symm
    have oinv : _root_.GlobalTheory.SmGL.ord k ϖ⁻¹ = -1 := by
      have h := _root_.GlobalTheory.SmGL.ord_mul k ϖ ϖ⁻¹
      rw [mul_inv_cancel, hord,
        _root_.GlobalTheory.SmGL.ord_eq_zero (x := (1 : kˣ)) (by simp only [Units.val_one, map_one])] at h
      omega
    have key : ∀ m : ℤ, _root_.GlobalTheory.SplitWeil.nabs k (ϖ ^ m) =
        (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-m) ∧ _root_.GlobalTheory.SmGL.ord k (ϖ ^ m) = m := by
      intro m
      refine Int.induction_on m ?_ ?_ ?_
      · refine ⟨by simp [_root_.GlobalTheory.SplitWeil.nabs_one], ?_⟩
        rw [zpow_zero]
        exact _root_.GlobalTheory.SmGL.ord_eq_zero (by simp only [Units.val_one, map_one])
      · intro i ih
        rw [_root_.zpow_add_one, _root_.GlobalTheory.SplitWeil.nabs_mul, _root_.GlobalTheory.SmGL.ord_mul,
          ih.1, ih.2, habs, hord]
        refine ⟨?_, rfl⟩
        rw [neg_add, zpow_add₀ hq, _root_.zpow_neg_one]
      · intro i ih
        rw [_root_.zpow_sub_one, _root_.GlobalTheory.SplitWeil.nabs_mul, _root_.GlobalTheory.SmGL.ord_mul,
          ih.1, ih.2, hinv, oinv]
        refine ⟨?_, by ring⟩
        rw [show -(-(i : ℤ) - 1) = -(-(i : ℤ)) + 1 by ring, zpow_add₀ hq, _root_.zpow_one]
    set o := _root_.GlobalTheory.SmGL.ord k x
    have hy : _root_.GlobalTheory.SmGL.ord k (x * ϖ ^ (-o)) = 0 := by
      rw [_root_.GlobalTheory.SmGL.ord_mul, (key _).2]
      ring
    have hy1 : _root_.GlobalTheory.SplitWeil.nabs k (x * ϖ ^ (-o)) = 1 :=
      _root_.GlobalTheory.SmGL.nabs_eq_one k
        (_root_.GlobalTheory.SmGL.ord_eq_zero_iff.mp hy)
    have hx : x * ϖ ^ (-o) * ϖ ^ o = x := by
      rw [mul_assoc, ← _root_.zpow_add, neg_add_cancel, zpow_zero, mul_one]
    calc _root_.GlobalTheory.SplitWeil.nabs k x
        = _root_.GlobalTheory.SplitWeil.nabs k (x * ϖ ^ (-o) * ϖ ^ o) := by rw [hx]
      _ = (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-o) := by
        rw [_root_.GlobalTheory.SplitWeil.nabs_mul, hy1, (key o).1, one_mul]
  rw [CG.loc_eq_zpow (hν.1 w), Units.val_zpow_eq_zpow_val, hν.2.1 w, GlobalTheory.SmGL.val_absPow, hgeneral,
    GlobalTheory.LocLanglands.resCard_eq_normV, GlobalTheory.SmGL.SphCompletion.ord_completion]
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  have e : Formalism.UG.ordV E w x = -WithZero.log (Valued.v (x : w.adicCompletion E)) := by
    rw [Formalism.UG.ordV, dite_eq_right h0]
    conv_rhs => rw [← WithZero.coe_unzero h0]
    rfl
  rw [e, ← Complex.ofReal_cpow (by positivity), ← Real.rpow_intCast, ← Real.rpow_mul (by positivity),
    ← Complex.ofReal_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_zpow,
    ← Real.rpow_intCast, ← Real.rpow_mul (by positivity)]
  congr 2
  · simp [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  · push_cast
    ring

end PositivityTheory.RSHS.LocalComponentTwist

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.LocSubOf

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.PRep GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.LsTop

open PositivityTheory.RSHS.LS

theorem comp_ne {G U V W : Type} [Monoid G] [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {a : Representation ℂ G U} {b : Representation ℂ G V} {c : Representation ℂ G W}
    (g : a.IntertwiningMap b) (hg : g.toLinearMap ≠ 0) (Φ : b.Equiv c) : ∃ f : a.IntertwiningMap c, f ≠ 0 := by
  refine ⟨Φ.toIntertwiningMap.comp g, fun h0 => hg ?_⟩
  refine LinearMap.ext fun v => Φ.toLinearEquiv.injective ?_
  have h1 := congrArg (fun q : a.IntertwiningMap c => q v) h0
  simpa using h1

theorem step1 (hR : RestrictAtPoint) (hP : ExistsProj) (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (N c : ℕ) (n : Fin c → ℕ) (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (w : HeightOneSpectrum (𝓞 E))
    (τ : ∀ i, SmIrr (GL (Fin (n i)) (w.adicCompletion E))) (hτ : ∀ i, (π i).IsLocComp w (τ i))
    (V : Submodule ℂ (Sm E N)) (hE : Emb V (· ∈ indForms h π)) (σ' : SmIrr (GL (Fin N) (w.adicCompletion E)))
    (hσ' : IsLocCompGL V w σ') :
    ∃ ℓ : σ'.V →ₗ[ℂ] PiTensorProduct ℂ fun i => (τ i).V, ℓ ≠ 0 ∧
      ∀ (p : parab (w.adicCompletion E) (stdBlocks n h)) (v : σ'.V),
        ℓ (σ'.ρ p v) = piTensor (fun i => (τ i).ρ) (leviProj (w.adicCompletion E) (stdBlocks n h) p) (ℓ v) := by
  obtain ⟨e, he1, he2, he3⟩ := hE
  obtain ⟨f, hf0, hfV, hfeq⟩ := hσ'
  let F : PositivityTheory.RSHS.LeviInductionForms.LocMaps (indForms h π) w σ'.ρ :=
    ⟨e ∘ₗ f, fun v => he1 _ (hfV v), fun g v => by
      simp only [LinearMap.comp_apply]
      rw [hfeq g v]
      exact he3 (.fin _) _ (hfV v)⟩
  have hF0 : F.1 ≠ 0 := by
    intro h0
    apply hf0
    refine LinearMap.ext fun v => ?_
    exact he2 _ (hfV v) (LinearMap.congr_fun h0 v)
  obtain ⟨L, hLT, hL0, hLeq⟩ := hR E N c n h π w σ'.V σ'.ρ F hF0
  obtain ⟨v0, hv0⟩ : ∃ v, L v ≠ 0 := by
    by_contra hc
    exact hL0 (LinearMap.ext fun v => not_not.1 fun hv => hc ⟨v, hv⟩)
  obtain ⟨p, hp0, hpeq⟩ := hP E c n π w τ hτ (L v0) (hLT v0) hv0
  refine ⟨p ∘ₗ L, fun h0 => hp0 (LinearMap.congr_fun h0 v0), fun q v => ?_⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hLeq q v]
  exact hpeq _ _ (hLT v)

theorem hst_rev (a d : ℕ) (i : Fin d) :
    ((-spehExp d i + a * spehExp d i : ℝ) : ℂ) =
      ((modExp (fun _ : Fin d => Fin a) i : ℤ) : ℂ) / 2 + (((d : ℂ) - 1) / 2 - ((i.rev : ℕ) : ℂ)) := by
  rw [PositivityTheory.RSHS.LocalComponentTwist.modExp_const, Fin.val_rev]
  have hi := i.2
  have hc : ((d - ((i : ℕ) + 1) : ℕ) : ℂ) = (d : ℂ) - ((i : ℕ) : ℂ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hc]
  unfold spehExp
  push_cast
  ring

theorem gen (hF : FrobRecip) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N a d : ℕ) (h : ∑ _ : Fin d, a = N) (σ : SmIrr (GL (Fin a) k)) (σ' : SmIrr (GL (Fin N) k))
    (ψ : Fin d → GL (Fin a) k →* ℂˣ)
    (hψ : ∀ i, ψ i = detChar (Fin a) (absPow k ((-spehExp d i + a * spehExp d i : ℝ) : ℂ)))
    (ℓ : σ'.V →ₗ[ℂ] PiTensorProduct ℂ fun _ : Fin d => σ.V) (h0 : ℓ ≠ 0)
    (hℓ : ∀ (p : parab k (stdBlocks (fun _ : Fin d => a) h)) (v : σ'.V), ℓ (σ'.ρ p v) =
      piTensor (fun i => GlobalTheory.SmGL.twist σ.ρ (ψ i)) (leviProj k (stdBlocks (fun _ : Fin d => a) h) p) (ℓ v)) :
    ∃ hd : ∑ i : Fin d, (spehFactor (IrrGL.of σ.ρ σ.smooth σ.irred) d i.rev).1 = N,
      ∃ f : σ'.ρ.IntertwiningMap (prodIrr (fun i : Fin d => spehFactor (IrrGL.of σ.ρ σ.smooth σ.irred) d i.rev) hd),
        f ≠ 0 := by
  have hx := hF k N d (fun _ => a) h σ' (PiTensorProduct ℂ fun _ : Fin d => σ.V)
    (piTensor (Γ := fun _ : Fin d => GL (Fin a) k) (X := fun _ : Fin d => σ.V) fun i => GlobalTheory.SmGL.twist σ.ρ (ψ i)) ℓ h0 hℓ
  have hy := PositivityTheory.RSHS.LocalComponentTwist.levi_equiv σ.ρ (fun i : Fin d => ((d : ℂ) - 1) / 2 - ((i.rev : ℕ) : ℂ))
    (fun i => ((-spehExp d i + a * spehExp d i : ℝ) : ℂ)) (hst_rev a d) ψ hψ
  refine hx.elim fun g hg => hy.elim fun φ => ?_
  let T : ∀ i : Fin d, (GlobalTheory.SmGL.twist σ.ρ (detChar (Fin a) (absPow k (((d : ℂ) - 1) / 2 - ((i.rev : ℕ) : ℂ))))).Equiv
      (spehFactor (IrrGL.of σ.ρ σ.smooth σ.irred) d i.rev).rep := fun i =>
    (twistEquiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred) _).trans
      ((IrrGL.of σ.ρ σ.smooth σ.irred).twEquiv _ (isSmoothChar_absPow _))
  let M := multiProdEquiv (stdBlocks (fun _ : Fin d => a) h) T
  exact ⟨h, comp_ne g hg ((GlobalTheory.LocGL.parIndEquiv (stdBlocks (fun _ : Fin d => a) h) φ).symm.trans M)⟩

theorem locSub_of (hR : RestrictAtPoint) (hP : ExistsProj) (hF : FrobRecip) : LocSub :=
  fun E _ _ _ N a d V π _ _ hA w σ σ' hσ hσ' =>
    hA.elim fun h hA => hA.elim fun ν hA =>
      (step1 hR hP E N d (fun _ => a) h (fun i => π.twist (ν i)) w
        (fun i => σ.twist (CuspSub.locDet a (ν i) w) (CuspSub.isOpen_ker_locDet (ν i) w))
        (fun i => PositivityTheory.RSHS.LocalComponentTwist.isLocComp_twist π (ν i) hσ) V hA.2 σ' hσ').elim fun ℓ hℓ =>
      gen hF (w.adicCompletion E) N a d h σ σ' (fun i => CuspSub.locDet a (ν i) w)
        (fun i => congrArg (fun χ : (w.adicCompletion E)ˣ →* ℂˣ => χ.comp Matrix.GeneralLinearGroup.det)
          (PositivityTheory.RSHS.LocalComponentTwist.loc_eq_absPow (hA.1 i) w)) ℓ hℓ.1 hℓ.2

end PositivityTheory.Rg.Rs.LsTop

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.AscSeedHolds2

section

@[expose] public section

namespace PositivityTheory.Rg.Rs

theorem locSub_holds2 : LocSub := LsTop.locSub_of C3.Rap.restrictAtPoint_holds existsProj2 frobRecip_holds

theorem ascSeed_holds2 : AscSeed := ascSeed_of_locSub locSub_holds2

end PositivityTheory.Rg.Rs
end
end
