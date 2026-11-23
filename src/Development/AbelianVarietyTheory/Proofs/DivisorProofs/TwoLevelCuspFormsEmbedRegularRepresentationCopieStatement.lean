module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LactMemDomOfIsom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesOfGroupDetermStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocyclePullbackRepresentationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormIndependentTranslatesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialCHolInvariantMemNonZeroDivisorsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPullbackPolynomialRightActionOfCocycleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsMulMemAddWeightStatement
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TwoLevelLogarithm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormPullbackIsBoundedSection
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemCuspFormsOfMultipleRationalIsometryMove
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LactMemDomOfIsom
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfSabMap
import Mathlib.Topology.Sheaves.Init

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsPullMem

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

namespace GlobalTheory.CuspEmb

theorem pull_mem_SS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C]
    (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ) (h : U), F ∈ M.SS la → M.pull h F ∈ M.SS la := by
  intro E _ _ _ r U C _ _ M la F h hF c
  have hm : GlobalTheory.LevelCusp.IsMatch (M.comp c).toData (M.comp (h • c)).toData (M.tr h c) :=
    { psi := (M.comp_Ψ c).trans (M.comp_Ψ (h • c)).symm
      p0 := (M.comp_basePoint c).trans (M.comp_basePoint (h • c)).symm
      xi := (M.comp_ξ0 c).trans (M.comp_ξ0 (h • c)).symm
      iso := fun u v => by
        show herm (M.comp (h • c)).Gm _ _ = herm (M.comp c).Gm u v
        rw [M.comp_Gm, M.comp_Gm]
        exact M.tr_herm h c u v
      lat := fun v => M.tr_Λ h c v }
  exact GlobalTheory.LevelCusp.mem_SS_of_isMatch E r _ _ (M.tr h c) hm (castWt (M.comp_Ψ c) la)
    (castWt (M.comp_Ψ (h • c)) la) (fun τ i => rfl) _ (fun y => F (h • c) (castFrame (M.comp_Ψ (h • c)) y)) 1
    (GlobalTheory.PullBdd.pull_isBddSec E r U C M la F hF h c).1 (hF (h • c)) (fun x _ => by rw [one_mul]; rfl)

end GlobalTheory.CuspEmb

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsPullMemStatement

section

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

theorem _root_.GlobalTheory.T.twoLevelCuspForms_pull_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ) (h : U), F ∈ M.SS la → M.pull h F ∈ M.SS la := by
  first | exact @GlobalTheory.CuspEmb.pull_mem_SS | exact GlobalTheory.CuspEmb.pull_mem_SS | (intros; apply GlobalTheory.CuspEmb.pull_mem_SS <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsRestrictHolInvariant

section

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspEmb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem isSec_cast (X : Data E r) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E) (p0 : ℕ)
    (h1 : X.Ψ = Ψ) (h2 : X.Gm = Gm) (h3 : X.p0 = p0) (la : Wt Ψ r) (G : Frame Ψ r → ℂ)
    (hG : X.IsSec (castWt h1 la) (fun x => G (castFrame h1 x))) :
    DifferentiableOn ℂ G (GG Ψ Gm p0) ∧
      ∀ γ ∈ X.Γ, ∀ x ∈ GG Ψ Gm p0, G (lact γ x) = X.χ (castWt h1 la) γ * G x := by
  subst h1 h2 h3
  exact ⟨hG.1, hG.2.2⟩

theorem res_mem_HA (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C]
    (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ) (hF : F ∈ M.SS la) : M.res F ∈ HA M := by
  have key := fun c => isSec_cast (M.comp c).toData M.Ψ M.Gm M.p0 (M.comp_Ψ c) (M.comp_Gm c) (M.comp_basePoint c) la (F c)
    (hF c).1.1
  refine ⟨fun c => ⟨F c, (key c).1, fun x => rfl⟩, fun c γ hγ x hx => ?_⟩
  show F c (lact γ x.1) = F c x.1
  rw [(key c).2 γ hγ x.1 x.2, M.χ_one c _ γ hγ, one_mul]

end GlobalTheory.CuspEmb

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsRestrictHolInvariantStatement

section

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

theorem _root_.GlobalTheory.T.twoLevelCuspForms_restrict_holInvariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ), F ∈ M.SS la → M.res F ∈ HA M := by
  first | exact @GlobalTheory.CuspEmb.res_mem_HA | exact GlobalTheory.CuspEmb.res_mem_HA | (intros; apply GlobalTheory.CuspEmb.res_mem_HA <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsEmbedRegularRepresentationCopie

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.CuspEmb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

def deg1 (M : TwoLevels E r U C) (W : Submodule ℂ (C → M.dom → ℂ)) : Submodule ℂ (Polynomial (HA M)) :=
  (W.comap (HA M).val.toLinearMap).map ((Polynomial.monomial 1).restrictScalars ℂ)

theorem mem_homogeneousExponentsOneBlock (M : TwoLevels E r U C) (W : Submodule ℂ (C → M.dom → ℂ)) (p : Polynomial (HA M)) :
    p ∈ deg1 M W ↔ ∃ f : HA M, (f : C → M.dom → ℂ) ∈ W ∧ Polynomial.monomial 1 f = p := Iff.rfl

def deg1Equiv (M : TwoLevels E r U C) (W : Submodule ℂ (C → M.dom → ℂ)) (hW : ∀ f ∈ W, f ∈ HA M) :
    W ≃ₗ[ℂ] deg1 M W :=
  LinearEquiv.ofBijective
    ({ toFun := fun f => ⟨Polynomial.monomial 1 ⟨f, hW f f.2⟩, (mem_homogeneousExponentsOneBlock M W _).2 ⟨⟨f, hW f f.2⟩, f.2, rfl⟩⟩
       map_add' := fun f g => Subtype.ext (by
         show Polynomial.monomial 1 (⟨((f + g : W) : C → M.dom → ℂ), hW _ (f + g).2⟩ : HA M) =
           Polynomial.monomial 1 ⟨f, hW _ f.2⟩ + Polynomial.monomial 1 ⟨g, hW _ g.2⟩
         rw [← map_add (f := _)]
         rfl)
       map_smul' := fun z f => Subtype.ext (by
         show Polynomial.monomial 1 (⟨((z • f : W) : C → M.dom → ℂ), hW _ (z • f).2⟩ : HA M) =
           z • Polynomial.monomial 1 ⟨f, hW _ f.2⟩
         rw [Polynomial.smul_monomial]
         rfl) } :
      W →ₗ[ℂ] deg1 M W)
    ⟨fun f g hfg => by
      have := congrArg Subtype.val hfg
      have := Polynomial.monomial_injective 1 this
      exact Subtype.ext (congrArg (fun q : HA M => (q : C → M.dom → ℂ)) this),
     fun p => by
      obtain ⟨f, hf, hp⟩ := (mem_homogeneousExponentsOneBlock M W p.1).1 p.2
      exact ⟨⟨f, hf⟩, Subtype.ext hp⟩⟩

theorem deg1Equiv_coe (M : TwoLevels E r U C) (W : Submodule ℂ (C → M.dom → ℂ)) (hW : ∀ f ∈ W, f ∈ HA M) (f : W) :
    ((deg1Equiv M W hW f : deg1 M W) : Polynomial (HA M)) = Polynomial.monomial 1 ⟨f, hW f f.2⟩ := rfl

theorem mul_pb_mem_cusp (M : TwoLevels E r U C) (ka mu : Wt M.Ψ r) (u0 : C → Frame M.Ψ r → ℂ) (hu0 : u0 ∈ M.SS mu)
    (k h : U) {f : C → M.dom → ℂ} (hf : f ∈ M.cusp ka) :
    f * pb M k (M.res u0) * pb M h (M.res u0) ∈ M.cusp (ka + 2 • mu) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨F, hF, rfl⟩ := hf
    have e : M.res F * pb M k (M.res u0) * pb M h (M.res u0) = M.res (F * M.pull k u0 * M.pull h u0) := rfl
    rw [e, two_smul, ← add_assoc]
    exact Submodule.subset_span ⟨_, GlobalTheory.T.twoLevelCuspForms_mul_mem_add_weight E r U C M _ _ _ _ (GlobalTheory.T.twoLevelCuspForms_mul_mem_add_weight E r U C M _ _ _ _ hF
      (GlobalTheory.T.twoLevelCuspForms_pull_mem E r U C M mu u0 k hu0)) (GlobalTheory.T.twoLevelCuspForms_pull_mem E r U C M mu u0 h hu0), rfl⟩
  | zero => simp
  | add f g _ _ hf hg => rw [add_mul, add_mul]; exact add_mem hf hg
  | smul z f _ hf => rw [smul_mul_assoc, smul_mul_assoc]; exact Submodule.smul_mem _ z hf

end GlobalTheory.CuspEmb


open GlobalTheory.CuspEmb in
theorem GlobalTheory.CuspEmb.cusp_embReg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U]
    [Finite C] [MulAction U C] (M : TwoLevels E r U C), ∀ (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)),
    IsPullRep M ka ρ → ∀ ep c : ℝ, Ranks M ka (sOf M) ep c → ∀ H : Subgroup U, LevelHyp (sub M H) →
    ∃ n : ℕ, GlobalTheory.BadCount.EmbReg ρ H n ∧ n * Nat.card H ≤ finrank ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M))) := by
  intro E _ _ _ r U C _ _ _ _ M ka ρ hρ ep c0 hR H hL
  classical
  haveI : Fintype U := Fintype.ofFinite U
  obtain ⟨u0, hu0, hdet⟩ := GlobalTheory.T.exists_cuspForm_independent_translates E r H C (sub M H) hL (sOf M) (even_sOf M) (le_sOf M)
  have hu0' : u0 ∈ M.SS (deMul M.Ψ r M.p0 (sOf M)) := hu0
  have hVHA : ∀ f ∈ M.cusp ka, f ∈ HA M := fun f hf => by
    refine (Submodule.span_le (p := Subalgebra.toSubmodule (HA M))).2 ?_ hf
    rintro _ ⟨F, hF, rfl⟩
    exact GlobalTheory.T.twoLevelCuspForms_restrict_holInvariant E r U C M ka F hF
  have h2HA : ∀ f ∈ M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M)), f ∈ HA M := fun f hf => by
    refine (Submodule.span_le (p := Subalgebra.toSubmodule (HA M))).2 ?_ hf
    rintro _ ⟨F, hF, rfl⟩
    exact GlobalTheory.T.twoLevelCuspForms_restrict_holInvariant E r U C M _ F hF
  obtain ⟨a, hcoc, hform⟩ := GlobalTheory.T.exists_cocycle_pullbackRepresentation E r U C M ka ρ hρ (fun f hf => (hVHA f hf).2)
  obtain ⟨h1, hlaw⟩ := GlobalTheory.T.twistedPullbackPolynomial_rightAction_of_cocycle E r U C M a hcoc
  let act : U →* (Polynomial (HA M) →ₐ[ℂ] Polynomial (HA M)) :=
    { toFun := fun k => tw M (fun c => (a k⁻¹ c : ℂ)) k⁻¹
      map_one' := by
        show tw M (fun c => (a 1⁻¹ c : ℂ)) 1⁻¹ = 1
        rw [inv_one]
        exact h1
      map_mul' := fun g h => by
        simp only [mul_inv_rev]
        rw [← hlaw]
        rfl }
  let ut : HA M := ⟨M.res u0, GlobalTheory.T.twoLevelCuspForms_restrict_holInvariant E r U C M _ u0 hu0'⟩
  have hact : ∀ k, act k (Polynomial.C ut) = Polynomial.C (pbA M k⁻¹ ut) := fun k => tw_C M _ _ _
  have hactm : ∀ k (f : HA M), act k (Polynomial.monomial 1 f) =
      Polynomial.monomial 1 (cst M (fun c => (a k⁻¹ c : ℂ)) * pbA M k⁻¹ f) := fun k f => tw_monomial_one M _ _ _

  have hnz : (Matrix.of fun h g : H => act ((h : U) * g) (Polynomial.C ut)).det ∈ nonZeroDivisors (Polynomial (HA M)) := by
    have e : (Matrix.of fun h g : H => act ((h : U) * g) (Polynomial.C ut)) =
        (Polynomial.C : HA M →+* Polynomial (HA M)).mapMatrix (Matrix.of fun h g : H => pbA M ((h : U) * g)⁻¹ ut) := by
      refine Matrix.ext fun h g => ?_
      simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hact, mul_inv_rev]
    rw [e, ← RingHom.map_det]
    refine GlobalTheory.T.polynomialC_holInvariant_mem_nonZeroDivisors E r U C M _ fun c => ?_
    obtain ⟨x, hx, hne⟩ := hdet c
    refine ⟨⟨x, hx⟩, ?_⟩
    let φ : HA M →+* ℂ := ((Pi.evalRingHom _ (⟨x, hx⟩ : M.dom)).comp (Pi.evalRingHom _ c)).comp (HA M).val.toRingHom
    have e2 : ((Matrix.of fun h g : H => pbA M ((h : U) * g)⁻¹ ut).det : C → M.dom → ℂ) c ⟨x, hx⟩ =
        φ (Matrix.of fun h g : H => pbA M ((h : U) * g)⁻¹ ut).det := rfl
    rw [e2, RingHom.map_det]
    have e3 : φ.mapMatrix (Matrix.of fun h g : H => pbA M ((h : U) * g)⁻¹ ut) =
        ((Matrix.of fun h h' : H => M.pull ((h : U) * h') u0 c x).submatrix (Equiv.inv H) (Equiv.inv H)).transpose := by
      ext h g
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
        Equiv.inv_apply, mul_inv_rev]
      rfl
    rw [e3, Matrix.det_transpose, Matrix.det_submatrix_equiv_self]
    exact hne

  let V := deg1 M (M.cusp ka)
  let V2 := deg1 M (M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M)))
  let V1 : Submodule ℂ (Polynomial (HA M)) :=
    Submodule.span ℂ {p | ∃ x ∈ V, ∃ h : H, p = x * act h (Polynomial.C ut)}
  let e := deg1Equiv M (M.cusp ka) hVHA
  let e2 := deg1Equiv M _ h2HA
  haveI : Module.Finite ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M))) := hR.2.1
  haveI : FiniteDimensional ℂ V2 := LinearEquiv.finiteDimensional e2
  let ρ' : Representation ℂ U V :=
    { toFun := fun k => e.toLinearMap ∘ₗ ρ k ∘ₗ e.symm.toLinearMap
      map_one' := by ext; simp
      map_mul' := fun g h => by ext; simp }
  have hρ' : ∀ g x, ((ρ' g x : V) : Polynomial (HA M)) = act g x := by
    intro g x
    obtain ⟨f, rfl⟩ := e.surjective x
    have e1 : ρ' g (e f) = e (ρ g f) := by simp [ρ']
    rw [e1, deg1Equiv_coe, deg1Equiv_coe, hactm]
    congr 1
    apply Subtype.ext
    funext c x
    have := hform g⁻¹ f c x
    rw [inv_inv] at this
    exact this
  have hV1 : ∀ h : H, ∀ x ∈ V, x * act h (Polynomial.C ut) ∈ V1 := fun h x hx => Submodule.subset_span ⟨x, hx, h, rfl⟩
  have hactV : ∀ (k : U), ∀ x ∈ V, act k x ∈ V := fun k x hx => by
    have := hρ' k ⟨x, hx⟩
    rw [← this]
    exact (ρ' k ⟨x, hx⟩).2
  have hV1s : ∀ h : H, ∀ x ∈ V1, act h x ∈ V1 := by
    intro h x hx
    induction hx using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨y, hy, k, rfl⟩ := hp
      refine Submodule.subset_span ⟨act h y, hactV h y hy, h * k, ?_⟩
      rw [map_mul, Subgroup.coe_mul, map_mul act]
      rfl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul z x _ hx => rw [map_smul]; exact Submodule.smul_mem _ z hx
  have hV2 : ∀ h : H, ∀ x ∈ V1, x * act h (Polynomial.C ut) ∈ V2 := by
    intro h x hx
    induction hx using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨y, hy, k, rfl⟩ := hp
      obtain ⟨f, hf, rfl⟩ := (mem_homogeneousExponentsOneBlock M _ y).1 hy
      rw [hact, hact, Polynomial.monomial_mul_C, Polynomial.monomial_mul_C]
      refine (mem_homogeneousExponentsOneBlock M _ _).2 ⟨_, ?_, rfl⟩
      exact mul_pb_mem_cusp M ka _ u0 hu0' _ _ hf
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | smul z x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ z hx
  obtain ⟨n, ⟨j, hj, hjeq⟩, hn⟩ := GlobalTheory.T.embedsInRegularRepresentationCopies_of_groupDeterminant ℂ U (Polynomial (HA M)) act H (Polynomial.C ut) hnz V V1 V2 ρ' hρ' hV1
    hV1s hV2
  refine ⟨n, ⟨j ∘ₗ e.toLinearMap, hj.comp e.injective, fun h v i => ?_⟩, ?_⟩
  · have := hjeq h (e v) i
    have e1 : ρ' h (e v) = e (ρ h v) := by simp [ρ']
    rw [e1] at this
    exact this
  · rw [← e2.finrank_eq] at hn
    exact hn

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsEmbedRegularRepresentationCopieStatement

section

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.twoLevelCuspForms_embed_regularRepresentation_copies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C] (M : TwoLevels E r U C), ∀ (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → ∀ ep c : ℝ, Ranks M ka (sOf M) ep c → ∀ H : Subgroup U, LevelHyp (sub M H) → ∃ n : ℕ, GlobalTheory.BadCount.EmbReg ρ H n ∧ n * Nat.card H ≤ finrank ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M))) := by
  first | exact @GlobalTheory.CuspEmb.cusp_embReg | exact GlobalTheory.CuspEmb.cusp_embReg | (intros; apply GlobalTheory.CuspEmb.cusp_embReg <;> assumption)
end
end
