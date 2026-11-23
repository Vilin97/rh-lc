module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.FractionRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEvalFixedOfFixedStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingBasisEvalStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingFrobeniusCompatStatement
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingGaloisEquivariant

section

@[expose] public section

open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobPairing

theorem T_gal {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀]
    [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀)
    (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)) (σA : A →+* A) (σC : C₀ →+* C₀)
    (gT : A ⊗[W] L →+ A ⊗[W] L) (hg : ∀ a y, gT (a ⊗ₜ y) = σA a ⊗ₜ y)
    (hσ : ∀ a, σC (c a) = c (σA a)) (hσk : ∀ x, σC (k x) = k x)
    (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L) :
    T c k hk f (gT z) = σC (T c k hk f z) := by
  refine TensorProduct.inductionOn z ?_ ?_
  · intro a y
    rw [hg]
    simp only [T, TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_mul, hσ, hσk]
  · intro x y hx hy
    simp only [map_add (f := _), hx, hy]

end GlobalTheory.CompanionTheory.FrobPairing
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingGaloisEquivariantStatement

section

@[expose] public section

open TensorProduct CrystallineSemistableComparison.Pb.Psi

theorem _root_.GlobalTheory.T.trace_pairing_galois_equivariant : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ (σA : A →+* A) (σC : C₀ →+* C₀) (gT : A ⊗[W] L →+ A ⊗[W] L), (∀ a y, gT (a ⊗ₜ y) = σA a ⊗ₜ y) → (∀ a, σC (c a) = c (σA a)) → (∀ x, σC (k x) = k x) → ∀ (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L), T c k hk f (gT z) = σC (T c k hk f z) := by
  first | exact @GlobalTheory.CompanionTheory.FrobPairing.T_gal | exact GlobalTheory.CompanionTheory.FrobPairing.T_gal | (intros; apply GlobalTheory.CompanionTheory.FrobPairing.T_gal <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingLTensorNaturality

section

@[expose] public section

open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobPsi

theorem T_lTensor {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A]
    {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L]
    (c : A →+* C₀) (k : K₀ →+* C₀)
    (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w))
    {L' : Type 1} [AddCommGroup L'] [Module W L'] (g : L' →ₗ[W] L)
    (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L') :
    T c k hk f (LinearMap.lTensor A g z) = T c k hk (f ∘ₗ g.baseChange K₀) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a y =>
    rw [LinearMap.lTensor_tmul, T_tmul, T_tmul, LinearMap.comp_apply, LinearMap.baseChange_tmul]
  | add z z' hz hz' => simp only [map_add (f := _), hz, hz']

end GlobalTheory.CompanionTheory.FrobPsi
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingLTensorNaturalityStatement

section

@[expose] public section

open TensorProduct CrystallineSemistableComparison.Pb.Psi

theorem _root_.GlobalTheory.T.trace_pairing_lTensor_naturality : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)) {L' : Type 1} [AddCommGroup L'] [Module W L'] (g : L' →ₗ[W] L) (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L'), T c k hk f (LinearMap.lTensor A g z) = T c k hk (f ∘ₗ g.baseChange K₀) z := by
  first | exact @GlobalTheory.CompanionTheory.FrobPsi.T_lTensor | exact GlobalTheory.CompanionTheory.FrobPsi.T_lTensor | (intros; apply GlobalTheory.CompanionTheory.FrobPsi.T_lTensor <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingSmulDual

section

@[expose] public section

open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobPsi

theorem T_ksmul : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ (x : K₀) (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L), T c k hk (x • f) z = k x * T c k hk f z := by
  intro W A C₀ _ _ _ _ K₀ _ _ L _ _ c k hk x f z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    rw [T_tmul, T_tmul, LinearMap.smul_apply, smul_eq_mul, map_mul]
    ring
  | add z z' hz hz' => rw [map_add (f := _), map_add (f := _), hz, hz', mul_add]

end GlobalTheory.CompanionTheory.FrobPsi
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingSmulDualStatement

section

@[expose] public section

open TensorProduct CrystallineSemistableComparison.Pb.Psi

theorem _root_.GlobalTheory.T.trace_pairing_smul_dual : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ (x : K₀) (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L), T c k hk (x • f) z = k x * T c k hk f z := by
  first | exact @GlobalTheory.CompanionTheory.FrobPsi.T_ksmul | exact GlobalTheory.CompanionTheory.FrobPsi.T_ksmul | (intros; apply GlobalTheory.CompanionTheory.FrobPsi.T_ksmul <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingSmulLeft

section

@[expose] public section

open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobPairing

theorem T_smul {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A]
    {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L]
    (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w))
    (f : Module.Dual K₀ (K₀ ⊗[W] L)) (a : A) (z : A ⊗[W] L) :
    T c k hk f (a • z) = c a * T c k hk f z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, mul_zero]
  | tmul b y =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    simp only [T, TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_mul, mul_assoc]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, mul_add]

end GlobalTheory.CompanionTheory.FrobPairing
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingSmulLeftStatement

section

@[expose] public section

open TensorProduct CrystallineSemistableComparison.Pb.Psi

theorem _root_.GlobalTheory.T.trace_pairing_smul_left : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ (f : Module.Dual K₀ (K₀ ⊗[W] L)) (a : A) (z : A ⊗[W] L), T c k hk f (a • z) = c a * T c k hk f z := by
  first | exact @GlobalTheory.CompanionTheory.FrobPairing.T_smul | exact GlobalTheory.CompanionTheory.FrobPairing.T_smul | (intros; apply GlobalTheory.CompanionTheory.FrobPairing.T_smul <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TLTensor

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open TensorProduct

namespace CrystallineSemistableComparison.Pb.Psi

variable {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A]
  {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L]
  (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w))

theorem T_smul (f : Module.Dual K₀ (K₀ ⊗[W] L)) (a : A) (z : A ⊗[W] L) : T c k hk f (a • z) = c a * T c k hk f z := GlobalTheory.T.trace_pairing_smul_left c k hk f a z

theorem T_ksmul (x : K₀) (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L) : T c k hk (x • f) z = k x * T c k hk f z := GlobalTheory.T.trace_pairing_smul_dual c k hk x f z

theorem T_gal (σA : A →+* A) (σC : C₀ →+* C₀) (gT : A ⊗[W] L →+ A ⊗[W] L) (hg : ∀ a y, gT (a ⊗ₜ y) = σA a ⊗ₜ y)
    (hσ : ∀ a, σC (c a) = c (σA a)) (hσk : ∀ x, σC (k x) = k x) (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L) :
    T c k hk f (gT z) = σC (T c k hk f z) := GlobalTheory.T.trace_pairing_galois_equivariant c k hk σA σC gT hg hσ hσk f z

theorem T_phi {F : W →+* W} (φA : A →+* A) (φC : C₀ →+* C₀) (φL : L →ₛₗ[F] L) (fr : K₀ →+* K₀)
    (φD : K₀ ⊗[W] L →+ K₀ ⊗[W] L) (hD : ∀ x y, φD (x ⊗ₜ y) = fr x ⊗ₜ φL y)
    (pT : A ⊗[W] L →+ A ⊗[W] L) (hp : ∀ a y, pT (a ⊗ₜ y) = φA a ⊗ₜ φL y)
    (hφ : ∀ a, φC (c a) = c (φA a)) (hφk : ∀ x, φC (k x) = k (fr x))
    {m : ℕ} (b : Module.Basis (Fin m) K₀ (K₀ ⊗[W] L)) (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L) :
    T c k hk f (pT z) = ∑ s, φC (T c k hk (b.coord s) z) * k (f (φD (b s))) :=
  GlobalTheory.T.trace_pairing_frobenius_compat c k hk φA φC φL fr φD hD pT hp hφ hφk b f z

theorem T_lTensor {L' : Type 1} [AddCommGroup L'] [Module W L'] (g : L' →ₗ[W] L) (f : Module.Dual K₀ (K₀ ⊗[W] L))
    (z : A ⊗[W] L') : T c k hk f (LinearMap.lTensor A g z) = T c k hk (f ∘ₗ g.baseChange K₀) z :=
  GlobalTheory.T.trace_pairing_lTensor_naturality c k hk g f z

theorem T_fac {B : Type} [Field B] (ι : C₀ →+* B) (i : A →+* B) (hι : ∀ a, ι (c a) = i a) (h : L →+ B)
    (hh : ∀ (w : W) y, h (w • y) = i (algebraMap W A w) * h y) {m : ℕ} (b : Module.Basis (Fin m) K₀ (K₀ ⊗[W] L)) :
    ∃ E : K₀ ⊗[W] L →+ B, (∀ x y, E (x ⊗ₜ y) = ι (k x) * h y) ∧
      ∀ G : A ⊗[W] L →+ B, (∀ a y, G (a ⊗ₜ y) = i a * h y) → ∀ z, G z = ∑ s, ι (T c k hk (b.coord s) z) * E (b s) :=
  GlobalTheory.T.trace_pairing_basis_eval c k hk ι i hι h hh b

theorem E_fix {B : Type} [Field B] [IsFractionRing W K₀] (ι : C₀ →+* B) (σB : B →+* B) (h : L →+ B)
    (E : K₀ ⊗[W] L →+ B) (hE : ∀ x y, E (x ⊗ₜ y) = ι (k x) * h y)
    (hσ : ∀ w, σB (ι (k (algebraMap W K₀ w))) = ι (k (algebraMap W K₀ w))) (hy : ∀ y, σB (h y) = h y) (v : K₀ ⊗[W] L) :
    σB (E v) = E v := GlobalTheory.T.tensor_eval_fixed_of_fixed k ι σB h E hE hσ hy v

end CrystallineSemistableComparison.Pb.Psi
end
end
end
