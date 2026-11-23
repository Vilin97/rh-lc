module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.StepSt
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix
import Mathlib.Tactic.Linter.HaveILetI
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.RealPowerProductEqOne
public import Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.ExtBasis
public import Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.GermUnique
public import Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.IsCompactSupport
public import Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.IsCompactSupportSB
public import Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.MeasurableSetBallM
public import Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.MemBallMSelf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.ValLeOneOfLc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds

-- Source module: Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.DetNeZeroOfNearOne

section

@[expose] public section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3

namespace PositivityTheory.Tls2.Ming3.RkX

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_ne_zero_of_near_one {j : ℕ} (A : Matrix (Fin j) (Fin j) k)
    (hA : ∀ i l, valuation k (A i l - (1 : Matrix (Fin j) (Fin j) k) i l) < 1) : A.det ≠ 0 := by
  have hint : ∀ i l, A i l ∈ 𝒪[k] := by
    intro i l
    have h1 : valuation k ((1 : Matrix (Fin j) (Fin j) k) i l) ≤ 1 := by
      by_cases h : i = l
      · subst h; simp
      · simp [Matrix.one_apply_ne h]
    have : A i l = (A i l - (1 : Matrix (Fin j) (Fin j) k) i l) + (1 : Matrix (Fin j) (Fin j) k) i l := by ring
    show valuation k (A i l) ≤ 1
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le (hA i l).le h1)
  let y : Matrix (Fin j) (Fin j) 𝒪[k] := Matrix.of fun i l => ⟨A i l, hint i l⟩
  have hy : (algebraMap 𝒪[k] k).mapMatrix y = A := by
    ext i l; rfl
  have hres : (IsLocalRing.residue 𝒪[k]).mapMatrix y = 1 := by
    ext i l
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [show (1 : Matrix (Fin j) (Fin j) (IsLocalRing.ResidueField 𝒪[k])) i l
        = IsLocalRing.residue 𝒪[k] ((1 : Matrix (Fin j) (Fin j) 𝒪[k]) i l) by
      by_cases h : i = l
      · subst h; simp
      · simp [Matrix.one_apply_ne h]]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
    have e : algebraMap 𝒪[k] k (y i l - (1 : Matrix (Fin j) (Fin j) 𝒪[k]) i l)
        = A i l - (1 : Matrix (Fin j) (Fin j) k) i l := by
      by_cases h : i = l
      · subst h; simp [y]; rfl
      · simp [y, Matrix.one_apply_ne h]; rfl
    rw [e]
    exact (hA i l).ne
  have hdet : IsLocalRing.residue 𝒪[k] y.det = 1 := by
    rw [RingHom.map_det, hres, Matrix.det_one]
  intro h0
  have : y.det = 0 := by
    apply Subtype.ext
    have := congrArg (fun M => M.det) hy
    rw [← RingHom.map_det] at this
    rw [← this] at h0
    exact h0
  rw [this, map_zero] at hdet
  exact zero_ne_one hdet

end PositivityTheory.Tls2.Ming3.RkX

namespace PositivityTheory.Tls2.Ming3

theorem rk : RkSt := by
  intro k _ _ _ _ n r j hjn hjr c hc x hx
  let A : Matrix (Fin j) (Fin j) k := x.submatrix (Fin.castLE hjn) (Fin.castLE hjr)
  have hA : ∀ i l, valuation k (A i l - (1 : Matrix (Fin j) (Fin j) k) i l) < 1 := by
    intro i l
    have h := hx (Fin.castLE hjn i) (Fin.castLE hjr l)
    have e : idem k r n j (Fin.castLE hjn i) (Fin.castLE hjr l) = (1 : Matrix (Fin j) (Fin j) k) i l := by
      show (if (i : ℕ) = l ∧ (l : ℕ) < j then (1 : k) else 0) = _
      by_cases h : i = l
      · subst h; simp
      · have h' : (i : ℕ) ≠ l := fun e => h (Fin.ext e)
        simp [Matrix.one_apply_ne h, h']
    rw [e] at h
    exact h.trans_lt hc
  have hdet := RkX.det_ne_zero_of_near_one A hA
  have h1 : A.rank = j := by
    rw [Matrix.rank_of_isUnit A ((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hdet))]
    simp
  calc j = A.rank := h1.symm
    _ ≤ x.rank := Matrix.rank_submatrix_le x _ _

end PositivityTheory.Tls2.Ming3
end
end

-- Source module: Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.Imports

section

@[expose] public section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3

namespace PositivityTheory.Tls2.Ming3

theorem cov : CovSt := by
  intro k _ _ _ _ _ _ ν hν n r h g Φ
  haveI : ν.IsAddHaarMeasure := hν.1
  rw [GlobalTheory.SplitWeil.integral_comp_mul_mul_volM ν g h Φ]
  simp only [Fintype.card_fin, Complex.real_smul]

end PositivityTheory.Tls2.Ming3
end
end

-- Source module: Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.LFrob

section

@[expose] public section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3
open scoped TensorProduct

noncomputable section

namespace PositivityTheory.Tls2.Ming3.FrobX

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {μ : kˣ →* ℂˣ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (GL (Fin r) k) V} {π : Representation ℂ (GL (Fin (r + t)) k) W}

abbrev lrep (t : ℕ) (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) :
    Representation ℂ (Levi k (Two (Fin r) (Fin t))) (V ⊗[ℂ] ℂ) :=
  (extTensor σ (detRep (Fin t) μ)).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem lrep_tmul (g : Levi k (Two (Fin r) (Fin t))) (v : V) :
    lrep t μ σ g (v ⊗ₜ[ℂ] (1 : ℂ)) =
      (μ (Matrix.GeneralLinearGroup.det (g true : GL (Fin t) k)) : ℂ) •
        (σ (g false : GL (Fin r) k) v ⊗ₜ[ℂ] (1 : ℂ)) := by
  change σ (g false) v ⊗ₜ[ℂ] ((μ (Matrix.GeneralLinearGroup.det (g true : GL (Fin t) k)) : ℂ) • (1 : ℂ)) = _
  rw [TensorProduct.tmul_smul]

def fn (π : Representation ℂ (GL (Fin (r + t)) k) W) (ev : W →ₗ[ℂ] V) (w : W) :
    GL (Fin (r + t)) k → V ⊗[ℂ] ℂ :=
  fun h => ev (π h w) ⊗ₜ[ℂ] (1 : ℂ)

theorem fn_law {ev : W →ₗ[ℂ] V} (hl : ParLaw μ σ π ev) (w : W)
    (p : parab k (two (stdSum (rfl : r + t = r + t)))) (g : GL (Fin (r + t)) k) :
    fn π ev w (p * g) =
      ((twist (lrep t μ σ) (deltaHalf k (Two (Fin r) (Fin t)))).comp
        (leviProj k (two (stdSum (rfl : r + t = r + t))))) p (fn π ev w g) := by
  rw [MonoidHom.comp_apply, GlobalTheory.SmGL.twist_apply]
  simp only [PositivityTheory.Tls2.Ming3.FrobX.fn]
  rw [PositivityTheory.Tls2.Ming3.FrobX.lrep_tmul, smul_smul, TensorProduct.smul_tmul', map_mul,
    Module.End.mul_apply, hl p (π g w)]

def elt (hπ : IsSmooth π) {ev : W →ₗ[ℂ] V} (hl : ParLaw μ σ π ev) (w : W) :
    IndSp (two (stdSum (rfl : r + t = r + t))) (lrep t μ σ) :=
  ⟨⟨fn π ev w, fun p g => fn_law hl w p g⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset ((hπ w).mem_nhds (by simp)) (by
      intro g hg
      have hg' : π g w = w := hg
      refine Subtype.ext (funext fun x => ?_)
      show fn π ev w (x * g) = fn π ev w x
      simp only [fn, map_mul, Module.End.mul_apply, hg']))⟩

def frobMap (hπ : IsSmooth π) {ev : W →ₗ[ℂ] V} (hl : ParLaw μ σ π ev) :
    π.IntertwiningMap (prod₂ σ (detRep (Fin t) μ)) where
  toFun w := elt hπ hl w
  map_add' w w' := Subtype.ext (Subtype.ext (funext fun h => by
    show ev (π h (w + w')) ⊗ₜ[ℂ] (1 : ℂ) = ev (π h w) ⊗ₜ[ℂ] (1 : ℂ) + ev (π h w') ⊗ₜ[ℂ] (1 : ℂ)
    simp [TensorProduct.add_tmul]))
  map_smul' c w := Subtype.ext (Subtype.ext (funext fun h => by
    show ev (π h (c • w)) ⊗ₜ[ℂ] (1 : ℂ) = c • (ev (π h w) ⊗ₜ[ℂ] (1 : ℂ))
    simp [TensorProduct.smul_tmul']))
  isIntertwining' g := by
    refine LinearMap.ext fun w => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show ev (π x (π g w)) ⊗ₜ[ℂ] (1 : ℂ) = ev (π (x * g) w) ⊗ₜ[ℂ] (1 : ℂ)
    rw [map_mul, Module.End.mul_apply]

end PositivityTheory.Tls2.Ming3.FrobX

namespace PositivityTheory.Tls2.Ming3

theorem frob : FrobSt := by
  intro k _ _ _ _ r t μ V _ _ W _ _ σ π ev hπ hev hl
  refine ⟨PositivityTheory.Tls2.Ming3.FrobX.frobMap hπ hl, fun h => hev ?_⟩
  refine LinearMap.ext fun w => ?_
  have h1 : ev (π 1 w) ⊗ₜ[ℂ] (1 : ℂ) = 0 :=
    congrArg (fun x => x.1.1 (1 : GL (Fin (r + t)) k)) (LinearMap.congr_fun h w)
  rw [map_one, Module.End.one_apply] at h1
  have h2 := congrArg (TensorProduct.rid ℂ V) h1
  rw [TensorProduct.rid_tmul, one_smul, map_zero] at h2
  rw [LinearMap.zero_apply]
  exact h2

end PositivityTheory.Tls2.Ming3
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.RepInvApply

section

@[expose] public section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3

namespace PositivityTheory.Rg.Ming

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem idem_eq_eMat (r t : ℕ) : idem k r (r + t) r = GlobalTheory.GodementJacquet.eMat k r t := by
  ext i l
  simp [idem, GlobalTheory.GodementJacquet.eMat]

theorem rank_eq_of_ne {r t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (Φ : SB (Matrix (Fin (r + t)) (Fin r) k))
    (hΦ : ∀ x : Matrix (Fin (r + t)) (Fin r) k, x.rank < r → Φ.1 x = 0)
    (x : Matrix (Fin (r + t)) (Fin r) k) (hx : Φ.1 x ≠ 0) : x.rank = r := by
  have h1 : x.rank ≤ r := by
    simpa using Matrix.rank_le_width x
  have h2 : ¬ x.rank < r := fun h => hx (hΦ x h)
  omega

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem rep_inv_apply {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL (Fin n) k) W) (h : GL (Fin n) k) (w : W) : π h (π h⁻¹ w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

end PositivityTheory.Rg.Ming

namespace PositivityTheory.Rg.Ming

theorem nz : BallSt → LocSt → NfSt → NzSt := by
  intro hball hloc hnf k _ _ _ _ _ _ ν hν r t μ V _ _ W _ _ σ π B hEq hG Φ hΦ
  ext w
  show B Φ w = 0
  set e := GlobalTheory.GodementJacquet.eMat k r t with he
  have key := hloc k (r + t) r (LinearMap.ker (B.flip w)) Φ
  have hmem := key ?_
  · simpa using hmem
  intro x hx
  have hrk := rank_eq_of_ne (V := V) (W := W) Φ hΦ x hx
  obtain ⟨⟨H, G, hxHG⟩, -⟩ := hnf k (r + t) r r x hrk
  rw [idem_eq_eMat] at hxHG
  obtain ⟨c, hc⟩ := hG (π H⁻¹ w)
  let f : Matrix (Fin (r + t)) (Fin r) k → Matrix (Fin (r + t)) (Fin r) k :=
    fun z => (H⁻¹ : GL (Fin (r + t)) k).val * z * (G⁻¹ : GL (Fin r) k).val
  have hf : Continuous f := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine ⟨f ⁻¹' ballM c e, ((hball k (r + t) r).1 c e).1.preimage hf, ?_, ?_⟩
  · show f x ∈ ballM c e
    have : f x = e := by
      simp only [f, hxHG, ← Matrix.mul_assoc]
      rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [this]
    exact fun i l => by simp
  · intro Ψ hΨ
    obtain ⟨Ψ', hΨ'def⟩ : ∃ Ψ' : SB (Matrix (Fin (r + t)) (Fin r) k),
        Ψ'.1 = om μ G H⁻¹ Ψ.1 :=
      ⟨⟨_, om_mem_SB μ _ _ Ψ.2⟩, rfl⟩
    have hΨΨ' : (Ψ : Matrix (Fin (r + t)) (Fin r) k → ℂ) = om μ G⁻¹ H Ψ'.1 := by
      show Ψ.1 = _
      rw [hΨ'def, ← om_mul, inv_mul_cancel, mul_inv_cancel, om_one]
    have hsupp : ∀ y, Ψ'.1 y ≠ 0 → y ∈ ballM c e := by
      intro y hy
      rw [hΨ'def] at hy
      simp only [om, inv_inv] at hy
      have h2 := (hΨ _ (right_ne_zero_of_mul hy)).1
      have h3 : f (H.val * y * G.val) = y := by
        simp only [f, ← Matrix.mul_assoc]
        rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      simpa [Set.mem_preimage, h3] using h2
    have h1 := hEq G⁻¹ H Ψ' Ψ hΨΨ' (π H⁻¹ w)
    rw [rep_inv_apply] at h1
    show B Ψ w = 0
    rw [h1, hc Ψ' hsupp, smul_zero, map_zero]

end PositivityTheory.Rg.Ming
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.MingZel

section

@[expose] public section

open MeasureTheory GlobalTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published ValuativeRel PositivityTheory.Tls2.Ming3 PositivityTheory.Rg.Ming
open scoped TensorProduct

namespace UpperTheory.Lit.HoweDuality

theorem lift_of_irr (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ)
    (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin (r + t)) k) W) (hrt : r < t)
    (hμs : IsSmoothChar μ) (hμu : IsUnitaryChar μ) (hσu : IsUnitarisable σ) (hπs : IsSmooth π) (hπi : π.IsIrreducible)
    (hIi : (prod₂ σ (detRep (Fin t) μ)).IsIrreducible) (hθ : ThetaPair μ σ π) :
    Nonempty (π.Equiv (prod₂ σ (detRep (Fin t) μ))) := by
  have hstep := step ball (loc ball) nf rk (core ball rk)
  have hgerm := germ ball
  have huniq := uniq ball
  have hnz := nz ball (loc ball) nf
  have hlaw := law ball cov
  obtain ⟨B, hB0, hE⟩ := hθ
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  obtain ⟨ν, hν⟩ := GlobalTheory.SplitWeil.Model.exists_isUnitVol (k := k)
  have down : ∀ j, j ≤ r → VanRk B j → VanRk B 0 := fun j => by
    induction j with
    | zero => exact fun _ h => h
    | succ j ih => exact fun hj h => ih (by omega) (hstep k (r + t) r μ V W σ π B j (by omega) (by omega) hμu hσu hE h)
  obtain ⟨ev, hev⟩ := huniq k ν hν (r + t) r V W B _ (hgerm k ν hν r t μ V W σ π B hμs hπs hE)
  have hev0 : ev ≠ 0 := fun e => hB0 (LinearMap.ext fun Φ => down r le_rfl
    (hnz k ν hν r t μ V W σ π B hE fun w => (hev w 0).2 (by rw [e]; rfl)) Φ fun _ h => absurd h (Nat.not_lt_zero _))
  obtain ⟨f, hf⟩ := frob k r t μ V W σ π ev hπs hev0 (hlaw k ν hν r t μ V W σ π B hE ev hev)
  haveI := hπi
  haveI := hIi
  rcases Representation.IsIrreducible.bijective_or_eq_zero f with h | h
  · exact ⟨.mk (LinearEquiv.ofBijective f.toLinearMap h) f.isIntertwining'⟩
  · exact absurd (by rw [h]; rfl) hf

end UpperTheory.Lit.HoweDuality
end
end
