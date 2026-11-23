module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralIntertwinesUnipotentStatement
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProjStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeOfProductInducedIso
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionLocallyConstantCompactStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinear
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentTopMemParabolicStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerOfFibIntEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinear
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothRightInv
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeOfProductInducedIsoStatement

section

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.derivative_of_product_induced_iso : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k i) (σ : GRep k t), IsSmooth τ.ρ → IsSmooth σ.ρ → Nonempty ((psiMinus k (prodPGn τ σ).ρ).Equiv (smInd (Qp k i t) (qRep (mtw τ (((t : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ))) → GIso (psiN (prodPGn τ σ)) ((psiN τ).prod σ) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.Norm.psiN_prodPGn_of_equiv | exact GlobalTheory.CompanionTheory.BZPsiPG.Norm.psiN_prodPGn_of_equiv | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.Norm.psiN_prodPGn_of_equiv <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralIntertwinesLevi

section

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibUnip

theorem map_smInt_translate {X Z Z' : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [MeasurableSpace X] [BorelSpace X] [AddCommGroup Z] [Module ℂ Z] [AddCommGroup Z'] [Module ℂ Z']
    (μ : MeasureTheory.Measure X) [μ.IsAddHaarMeasure]
    (L : Z →ₗ[ℂ] Z') (T : Z →ₗ[ℂ] Z) (hT : ∀ z, L (T z) = L z) (φ : X → Z) (m : X)
    (hl : IsLocallyConstant φ) (hc : HasCompactSupport φ) :
    L (smInt μ (fun v => T (φ (v + m)))) = L (smInt μ φ) := by
  obtain ⟨_, h2, h3, _⟩ := SmIntEl.smInt_properties (X := X) (W := Z) (W' := Z) μ
  have hl' : IsLocallyConstant (φ ∘ fun v => v + m) := hl.comp_continuous ((continuous_id.add continuous_const))
  have hc' : HasCompactSupport (φ ∘ fun v => v + m) :=
    hc.comp_homeomorph (Homeomorph.addRight m)
  have e1 : smInt μ (T ∘ (φ ∘ fun v => v + m)) = T (smInt μ (φ ∘ fun v => v + m)) := h2 T _ hl' hc'
  have e2 : smInt μ (φ ∘ fun v => v + m) = smInt μ φ :=
    h3 (fun v => v + m) φ (MeasureTheory.measurePreserving_add_right μ m) hl
  calc L (smInt μ (fun v => T (φ (v + m)))) = L (T (smInt μ (φ ∘ fun v => v + m))) :=
        congrArg L e1
    _ = L (smInt μ (φ ∘ fun v => v + m)) := hT _
    _ = L (smInt μ φ) := congrArg L e2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem midV_add (i t : ℕ) (v m : Fin t → k) :
    midV k i t (v + m) = midV k i t v + midV k i t m := by
  funext j
  induction j using Fin.addCases <;> simp [midV]

theorem mul_uM_eq (i t : ℕ) (g : GL (Fin (i + t)) k) (y : Fin (i + t) → k) (x : Fin i → k) (m v : Fin t → k)
    (hy : (g : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y = topV k i t x + midV k i t m) :
    uM k (i + t) (midV k i t v) * levi k (i + t) g * uM k (i + t) y =
      uM k (i + t) (topV k i t x) * (uM k (i + t) (midV k i t (v + m)) * levi k (i + t) g) := by
  have e : midV k i t v + (topV k i t x + midV k i t m) = topV k i t x + midV k i t (v + m) := by
    rw [midV_add]; abel
  rw [mul_assoc, levi_mul_uM, hy, ← mul_assoc, ← uM_add, e, uM_add, mul_assoc]

variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem clT_extTensor (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (x : Fin i → k) (z : V ⊗[ℂ] W) :
    clT τ W (extTensor τ σ (uM k i x, 1) z) = clT τ W z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
  | tmul a b =>
    have hq : (twKer τ (MirUin k i) 1).mkQ (τ (uM k i x) a) = (twKer τ (MirUin k i) 1).mkQ a := by
      refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨_, uM_mem k i x⟩, a, ?_⟩)
      simp
    rw [extTensor_tmul]
    simp only [clT, LinearMap.rTensor_tmul, map_one, Module.End.one_apply]
    exact congrArg (· ⊗ₜ[ℂ] b) hq



theorem fibV_prodPG (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) (y : Fin (i + t) → k)
    (x : Fin i → k) (m v : Fin t → k)
    (hy : (g : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y = topV k i t x + midV k i t m) :
    fibV (prodPG τ σ (uM k (i + t) y) f) g v = extTensor τ σ (uM k i x, 1) (fibV f g (v + m)) := by
  refine Exists.elim (GlobalTheory.T.unipotent_top_mem_parabolic k i t x) fun hmem hproj => ?_
  have e1 : fibV (prodPG τ σ (uM k (i + t) y) f) g v =
      f.1.1.1 (uM k (i + t) (midV k i t v) * levi k (i + t) g * uM k (i + t) y) := rfl
  have e2 := f.1.1.2 ⟨_, hmem⟩ (uM k (i + t) (midV k i t (v + m)) * levi k (i + t) g)
  calc fibV (prodPG τ σ (uM k (i + t) y) f) g v
      = f.1.1.1 (uM k (i + t) (topV k i t x) * (uM k (i + t) (midV k i t (v + m)) * levi k (i + t) g)) :=
        e1.trans (congrArg f.1.1.1 (mul_uM_eq i t g y x m v hy))
    _ = extTensor τ σ (pgProj k i t ⟨_, hmem⟩) (fibV f g (v + m)) := e2
    _ = extTensor τ σ (uM k i x, 1) (fibV f g (v + m)) :=
        congrArg (fun a => extTensor τ σ a (fibV f g (v + m))) hproj

theorem fibInt_col (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (hτ : IsSmooth τ) (hσ : IsSmooth σ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)]
    (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure]
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (y : Fin (i + t) → k) (g : GL (Fin (i + t)) k)
    (x : Fin i → k) (m : Fin t → k)
    (hxm : (g : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y = topV k i t x + midV k i t m) :
    fibInt μ (prodPG τ σ (uM k (i + t) y) f) g = fibInt μ f g := by
  have hlc := GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ f g
  have hfun : fibV (prodPG τ σ (uM k (i + t) y) f) g =
      fun v => (extTensor τ σ (uM k i x, 1)) (fibV f g (v + m)) :=
    funext fun v => fibV_prodPG τ σ f g y x m v hxm
  have h1 : clT τ W (smInt μ (fibV (prodPG τ σ (uM k (i + t) y) f) g)) =
      clT τ W (smInt μ fun v => (extTensor τ σ (uM k i x, 1)) (fibV f g (v + m))) :=
    congrArg (fun φ => clT τ W (smInt μ φ)) hfun
  exact h1.trans (map_smInt_translate μ (clT τ W) (extTensor τ σ (uM k i x, 1))
          (clT_extTensor τ σ x) (fibV f g) m hlc.1 hlc.2)



theorem fibInt_unip : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure], ∀ (f : cIndSpace (HPG k i t) (hRep τ σ)) (u : Mir k (i + t)), u ∈ MirUin k (i + t) → ∀ g : GL (Fin (i + t)) k, fibInt μ (prodPG τ σ u f) g = fibInt μ f g := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ _ _ μ _ f u hu g
  refine Exists.elim (exists_uM_of_mem k (i + t) hu) fun y hy => ?_
  refine Exists.elim (exists_top_mid k i t ((g : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y)) fun x hx => ?_
  refine Exists.elim hx fun m hxm => ?_
  exact (congrArg (fun u' => fibInt μ (prodPG τ σ u' f) g) hy).trans
    (fibInt_col τ σ hτ hσ μ f y g x m hxm)

end GlobalTheory.CompanionTheory.BZPsiPG.FibUnip

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralIntertwinesLeviStatement

section

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.fibre_integral_intertwines_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure], ∀ (f : cIndSpace (HPG k i t) (hRep τ σ)) (u : Mir k (i + t)), u ∈ MirUin k (i + t) → ∀ g : GL (Fin (i + t)) k, fibInt μ (prodPG τ σ u f) g = fibInt μ f g := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibUnip.fibInt_unip | exact GlobalTheory.CompanionTheory.BZPsiPG.FibUnip.fibInt_unip | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibUnip.fibInt_unip <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.HighestDerivativeProducts.IsSmoothCharDpowM

section

@[expose] public section

noncomputable section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
namespace GlobalTheory.CompanionTheory.BZPsiPG.Hand
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem fibInt_levi (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    [MeasurableSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (g' g : GL (Fin (i + t)) k) :
    fibInt μ (prodPG τ σ (levi k (i + t) g') f) g = fibInt μ f (g * g') := by
  have : fibV (prodPG τ σ (levi k (i + t) g') f) g = fibV f (g * g') := by
    funext v
    have e : uM k (i + t) (midV k i t v) * levi k (i + t) (g * g') =
        uM k (i + t) (midV k i t v) * levi k (i + t) g * levi k (i + t) g' := by
      rw [map_mul, mul_assoc]
    exact (congrArg f.1.1.1 e).symm
  exact congrArg (fun x => clT τ W (smInt μ x)) this

theorem isOpen_stab_of {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ G Z) (z : Z) (S : Set G) (hS : IsOpen S) (h1 : (1 : G) ∈ S) (h : ∀ s ∈ S, ρ s z = z) :
    IsOpen {g : G | ρ g z = z} := by
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have ho : IsOpen ((fun y => g⁻¹ * y) ⁻¹' S) := hS.preimage (by fun_prop)
  refine Filter.mem_of_superset (ho.mem_nhds (by simpa using h1)) fun y hy => ?_
  have e := h _ hy
  show ρ y z = z
  have : y = g * (g⁻¹ * y) := by group
  rw [this, map_mul, Module.End.mul_apply, e]
  exact hg

theorem isOpen_cInd_stab {τ : Representation ℂ (Mir k i) V} {σ : Representation ℂ (GL (Fin t) k) W}
    (f : cIndSpace (HPG k i t) (hRep τ σ)) : IsOpen {p | prodPG τ σ p f = f} := by
  have h : IsOpen {g | ind (HPG k i t) (hRep τ σ) g f.1.1 = f.1.1} := f.1.2
  have e : {p | prodPG τ σ p f = f} = {g | ind (HPG k i t) (hRep τ σ) g f.1.1 = f.1.1} := by
    ext p
    constructor
    · intro e
      exact congrArg (fun x : cIndSpace (HPG k i t) (hRep τ σ) => x.1.1) e
    · intro e
      exact Subtype.ext (Subtype.ext e)
  rw [e]
  exact h

section Map
variable (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (hτ : IsSmooth τ) (hσ : IsSmooth σ)
  [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure]

include hτ hσ

theorem fibInt_add (a b : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) :
    fibInt μ (a + b) g = fibInt μ a g + fibInt μ b g := by
  obtain ⟨a1, a2⟩ := GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ a g
  obtain ⟨b1, b2⟩ := GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ b g
  have e : fibV (a + b) g = fibV a g + fibV b g := by
    funext v
    exact map_add (evL (uM k (i + t) (midV k i t v) * levi k (i + t) g)) a b
  have h := (GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_properties (W := V ⊗[ℂ] W) (W' := V ⊗[ℂ] W) μ).1 _ _ a1 a2 b1 b2
  exact (congrArg (fun x => clT τ W (smInt μ x)) e).trans ((congrArg (clT τ W) h).trans (map_add _ _ _))

theorem fibInt_smul (c : ℂ) (a : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) :
    fibInt μ (c • a) g = c • fibInt μ a g := by
  obtain ⟨a1, a2⟩ := GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ a g
  have e : fibV (c • a) g = ((c • LinearMap.id : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] W)) ∘ fibV a g := by
    funext v
    exact map_smul (evL (uM k (i + t) (midV k i t v) * levi k (i + t) g)) c a
  have h := (GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_properties (W := V ⊗[ℂ] W) (W' := V ⊗[ℂ] W) μ).2.1
    (c • LinearMap.id : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] W) _ a1 a2
  exact (congrArg (fun x => clT τ W (smInt μ x)) e).trans ((congrArg (clT τ W) h).trans (map_smul (clT τ W) c _))

def phiInd (f : cIndSpace (HPG k i t) (hRep τ σ)) : indSpace (Qp k i t) (qRep τ σ) :=
  ⟨fibInt μ f, fun q g => GlobalTheory.T.fibre_integral_intertwines_unipotent k i t τ σ hτ hσ μ f q g⟩

theorem phiInd_right (f : cIndSpace (HPG k i t) (hRep τ σ)) (s : GL (Fin (i + t)) k)
    (hs : prodPG τ σ (levi k (i + t) s) f = f) :
    ind (Qp k i t) (qRep τ σ) s (phiInd τ σ hτ hσ μ f) = phiInd τ σ hτ hσ μ f := by
  apply Subtype.ext
  funext g
  exact (fibInt_levi τ σ μ f s g).symm.trans (congrArg (fun x => fibInt μ x g) hs)

theorem phiInd_mem (f : cIndSpace (HPG k i t) (hRep τ σ)) :
    phiInd τ σ hτ hσ μ f ∈ smoothPart (ind (Qp k i t) (qRep τ σ)) := by
  have h : IsOpen {g | ind (Qp k i t) (qRep τ σ) g (phiInd τ σ hτ hσ μ f) = phiInd τ σ hτ hσ μ f} :=
    isOpen_stab_of (ind (Qp k i t) (qRep τ σ)) _
      (levi k (i + t) ⁻¹' {p | prodPG τ σ p f = f})
      ((isOpen_cInd_stab f).preimage (GlobalTheory.T.continuous_levi_unipotent_proj k _).1)
      (by
        have h0 : levi k (i + t) (1 : GL (Fin (i + t)) k) = 1 := (levi k (i + t)).map_one
        have h1 : prodPG τ σ (1 : Mir k (i + t)) = 1 := (prodPG τ σ).map_one
        exact (congrArg (fun x => prodPG τ σ x f) h0).trans (LinearMap.congr_fun h1 f))
      (fun s hs => phiInd_right τ σ hτ hσ μ f s hs)
  exact h

def phiFun (f : cIndSpace (HPG k i t) (hRep τ σ)) : smoothPart (ind (Qp k i t) (qRep τ σ)) :=
  ⟨phiInd τ σ hτ hσ μ f, phiInd_mem τ σ hτ hσ μ f⟩

def phiLin : cIndSpace (HPG k i t) (hRep τ σ) →ₗ[ℂ] smoothPart (ind (Qp k i t) (qRep τ σ)) where
  toFun := phiFun τ σ hτ hσ μ
  map_add' a b := Subtype.ext (Subtype.ext (funext fun g => fibInt_add τ σ hτ hσ μ a b g))
  map_smul' c a := Subtype.ext (Subtype.ext (funext fun g => fibInt_smul τ σ hτ hσ μ c a g))

theorem phiLin_apply (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) :
    (phiLin τ σ hτ hσ μ f).1.1 g = fibInt μ f g := rfl

theorem twKer_le_ker : twKer (prodPG τ σ) (MirUin k (i + t)) 1 ≤ LinearMap.ker (phiLin τ σ hτ hσ μ) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨u, w, rfl⟩
  have e : phiLin τ σ hτ hσ μ (prodPG τ σ (u : Mir k (i + t)) w) = phiLin τ σ hτ hσ μ w :=
    Subtype.ext (Subtype.ext (funext fun g => GlobalTheory.T.fibre_integral_intertwines_levi k i t τ σ hτ hσ μ w (u : Mir k (i + t)) u.2 g))
  have e2 : (((1 : MirUin k (i + t) →* ℂˣ) u : ℂˣ) : ℂ) • w = w := by simp
  show phiLin τ σ hτ hσ μ _ = 0
  exact (congrArg (fun x => phiLin τ σ hτ hσ μ (prodPG τ σ (u : Mir k (i + t)) w - x)) e2).trans
    ((map_sub (phiLin τ σ hτ hσ μ) _ _).trans (sub_eq_zero.2 e))

theorem ker_le_twKer : LinearMap.ker (phiLin τ σ hτ hσ μ) ≤ twKer (prodPG τ σ) (MirUin k (i + t)) 1 := by
  intro f hf
  have h : phiLin τ σ hτ hσ μ f = 0 := hf
  exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.mem_twKer_of_fibInt_eq_zero k i t τ σ hτ hσ μ f fun g => congrFun (congrArg (fun x : smoothPart (ind (Qp k i t) (qRep τ σ)) => x.1.1) h) g

theorem phiLin_surj : Function.Surjective (phiLin τ σ hτ hσ μ) := by
  intro G
  have h := GlobalTheory.CompanionTheory.BZPsiPG.exists_fibInt_eq k i t τ σ hτ hσ μ G
  refine h.imp fun f hf => ?_
  have e : (phiLin τ σ hτ hσ μ f).1.1 = G.1.1 := funext fun g => (phiLin_apply τ σ hτ hσ μ f g).trans (hf g)
  exact Subtype.ext (Subtype.ext e)

theorem phiLin_levi (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) :
    phiLin τ σ hτ hσ μ (prodPG τ σ (levi k (i + t) g) f) = smInd (Qp k i t) (qRep τ σ) g (phiLin τ σ hτ hσ μ f) :=
  Subtype.ext (Subtype.ext (funext fun x => fibInt_levi τ σ μ f g x))

end Map

theorem twAct_equiv_of_map {G M Z Z' : Type} [Group G] [Group M] [AddCommGroup Z] [Module ℂ Z] [AddCommGroup Z'] [Module ℂ Z']
    (ρ : Representation ℂ G Z) (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) (ρ' : Representation ℂ M Z')
    (Φ : Z →ₗ[ℂ] Z') (hk : LinearMap.ker Φ = twKer ρ N θ) (hsurj : Function.Surjective Φ)
    (hint : ∀ m z, Φ (ρ (s m) z) = ρ' m (Φ z)) :
    Nonempty ((twAct ρ N θ s hs).Equiv ρ') := by
  let e : TwJacquet ρ N θ ≃ₗ[ℂ] Z' :=
    (Submodule.quotEquivOfEq _ _ hk.symm).trans (Φ.quotKerEquivOfSurjective hsurj)
  refine ⟨.mk e fun g => ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact hint g f

theorem core (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (hτ : IsSmooth τ) (hσ : IsSmooth σ) :
    Nonempty ((psiMinus k (prodPG τ σ)).Equiv (smInd (Qp k i t) (qRep τ σ))) := by
  letI : MeasurableSpace (Fin t → k) := borel _
  haveI : BorelSpace (Fin t → k) := ⟨rfl⟩
  exact twAct_equiv_of_map (prodPG τ σ) (MirUin k (i + t)) 1 (levi k (i + t)) (levi_normalises (i + t))
    (smInd (Qp k i t) (qRep τ σ)) (phiLin τ σ hτ hσ (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (Fin t → k)))
    (le_antisymm (ker_le_twKer τ σ hτ hσ _) (twKer_le_ker τ σ hτ hσ _))
    (phiLin_surj τ σ hτ hσ _) (fun g f => phiLin_levi τ σ hτ hσ _ f g)

theorem isSmoothChar_dpow (n : ℕ) (s : ℝ) : IsSmoothChar (dpow (k := k) n s) :=
  (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar

theorem isSmoothChar_dpowM (n : ℕ) (s : ℝ) : IsSmoothChar (dpowM (k := k) n s) :=
  (isSmoothChar_dpow (n + 1) s).comp _ continuous_subtype_val

theorem psiPG : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PsiPG k := by
  intro k _ _ _ _ i t τ σ hτ hσ
  exact GlobalTheory.T.derivative_of_product_induced_iso k i t τ σ hτ hσ
    (core _ _ (isSmooth_twist hτ (isSmoothChar_dpowM _ _)) (isSmooth_twist hσ (isSmoothChar_dpow _ _)))

end GlobalTheory.CompanionTheory.BZPsiPG.Hand
end
end
end
