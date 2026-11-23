module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.EmDefs
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbscissaConvergenceIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IpSmulRight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulInvSub
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IpSmulRight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedBlockFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulInvSub
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousIpFst

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
open IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.OrbExist

variable {D : D7} {a n r t : ℕ}

theorem continuous_qv (V : HSp D) (b₀ : HermE D r) :
    Continuous (fun z : Mx D V.rank r × Mx D V.rank t => qv V b₀ z) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hip : ∀ {X : Type} [TopologicalSpace X] {a c : ℕ} {f : X → Mx D V.rank a} {g : X → Mx D V.rank c},
      Continuous f → Continuous g → Continuous (fun x => ip V (f x) (g x)) := by
    intro X _ a c f g hf hg
    unfold ip
    exact (continuous_adj.comp hf).matrix_mul (continuous_const.matrix_mul hg)
  have hyv : Continuous (fun z : Mx D V.rank r × Mx D V.rank t => yv V b₀ z) := by
    unfold yv
    exact continuous_const.matrix_mul (hip continuous_fst continuous_snd)
  have hpr : Continuous (fun x : Mx D V.rank r × Mx D V.rank t => pr b₀ (yv V b₀ x) (yv V b₀ x)) := by
    unfold pr
    exact (continuous_adj.comp hyv).matrix_mul (continuous_const.matrix_mul hyv)
  unfold qv
  have h1 : Continuous (fun z : Mx D V.rank r × Mx D V.rank t => ip V z.2 z.2) := hip continuous_snd continuous_snd
  have hn : ContinuousNeg (AE D) := IsTopologicalRing.toContinuousNeg
  have ha : ContinuousAdd (AE D) := IsTopologicalSemiring.toContinuousAdd
  exact continuous_matrix fun i j => (h1.matrix_elem i j).add (hpr.matrix_elem i j).neg |>.congr fun z => (sub_eq_add_neg _ _).symm

theorem continuous_ip_fst (V : HSp D) :
    Continuous (fun z : Mx D V.rank r × Mx D V.rank t => ip V z.1 z.1) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  unfold ip
  exact (continuous_adj.comp continuous_fst).matrix_mul (continuous_const.matrix_mul continuous_fst)

theorem continuous_pch₂ {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {X : Type} [TopologicalSpace X]
    {f g : X → Mx D t t} (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => pch ψ (f x) (g x)) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have htr : Continuous (trA : AE D → AF D.host.F) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  have hhalf : Continuous (halfTr : AE D → AF D.host.F) := by
    unfold halfTr
    exact continuous_const.mul htr
  unfold pch
  exact hψ.1.comp (hhalf.comp (hf.matrix_mul hg).matrix_trace)

theorem isClosed_fixed (e : AE D) :
    IsClosed {z : Mx D a r × Mx D a t | e • z.1 = z.1 ∧ e • z.2 = z.2} := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, -, -, h1, -⟩ := GlobalTheory.CompanionTheory.ColumnSplitting.top_mx (D := D) a r
  obtain ⟨-, -, -, h2, -⟩ := GlobalTheory.CompanionTheory.ColumnSplitting.top_mx (D := D) a t
  have c1 : Continuous fun x : Mx D a r => e • x := continuous_const_smul e
  have c2 : Continuous fun x : Mx D a t => e • x := continuous_const_smul e
  exact (isClosed_eq (c1.comp continuous_fst) continuous_fst).inter (isClosed_eq (c2.comp continuous_snd) continuous_snd)

theorem conj_cancel (g : GL (Fin t) (AE D)) (q : Mx D t t) :
    mm (mm (adj (g⁻¹).1) (mm (mm (adj g.1) q) g.1)) (g⁻¹).1 = q := by
  have h1 : g.1 * (g⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : (adj (g⁻¹).1 * adj g.1 : Mx D t t) = 1 := by
    have := adj_mul (D := D) g.1 (g⁻¹).1
    rw [← this, h1, adj_one_r]
  simp only [mm]
  calc _ = (adj (g⁻¹).1 * adj g.1 : Mx D t t) * q * (g.1 * (g⁻¹).1) := by simp only [Matrix.mul_assoc]
    _ = q := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem comp_mem {θ : InfFam D} (hθ : IsInfFam θ) {hn : r + t = n} {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e)
    (hR : ∀ f ∈ algA (a := a) θ hn S e,
      ∃ Φ ∈ schwartzA θ a n, Good S e Φ ∧ HasCompactSupport Φ ∧ f = fun z => Φ (jn hn z.1.1 z.1.2))
    (hSt : AlgStab) (h : GL (Fin a) (AE D)) (g : GL (Fin n) (AE D)) (hh : e • (h.1 - 1) = h.1 - 1) (hg : e • (g.1 - 1) = g.1 - 1)
    (Θ : XS D a r t e → XS D a r t e)
    (hΘ : ∀ z, jn hn (Θ z).1.1 (Θ z).1.2 = mm (mm h.1 (jn hn z.1.1 z.1.2)) g.1) (f : XS D a r t e → ℂ)
    (hf : f ∈ algA (a := a) θ hn S e) : f ∘ Θ ∈ algA (a := a) θ hn S e := by
  obtain ⟨Φ, h1, h2, h3, rfl⟩ := hR f hf
  obtain ⟨m1, m2, m3⟩ := hSt D θ hθ a n S e hS h g hh hg Φ h1 h2 h3
  refine Submodule.subset_span ⟨_, m1, m2, m3, ?_⟩
  funext z
  simp only [Function.comp, hΘ]

theorem trans_int₁ {X N : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace N] [MeasurableSpace N]
    [BorelSpace N] (σ : Measure X) (lam : Measure N) (k : N → X → ℂ) (f : X → ℂ) (Θ : X ≃ₜ X)
    (h₁ : σ.map Θ = σ) (hk : ∀ x, ∀ᵐ z ∂σ, k x z = k x (Θ z)) :
    ∫ x, ∫ z, f (Θ z) * k x z ∂σ ∂lam = ((1 : ℝ≥0) : ℂ) * ∫ x, ∫ z, f z * k x z ∂σ ∂lam := by
  have := trans_int σ lam k f Θ (Homeomorph.refl N) 1 1 (by rw [one_smul]; exact h₁) (by simp) hk
  simpa using this

theorem kap (A : ℝ≥0) (hA : A ≠ 0) (N r t : ℕ) (hN : N = r + 2 * t) : (A⁻¹) ^ N * ((A⁻¹)⁻¹) ^ t = (A⁻¹) ^ (r + t) := by
  subst hN
  rw [inv_inv, two_mul, ← add_assoc, pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hA, one_pow, mul_one]

theorem absA_inv (D : D7) (u : (AE D)ˣ) : absA D u⁻¹ = (absA D u)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, inv_mul_cancel, map_one]

theorem absA_ne (D : D7) (u : (AE D)ˣ) : absA D u ≠ 0 := by
  have h1 : absA D u * absA D u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  intro h
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

end GlobalTheory.CompanionTheory.OrbExist

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestAlg

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.EisM

section Abstract

variable {X H : Type}

end Abstract

variable {D : D7} {N r t n : ℕ}

abbrev XS (e : AE D) (N r t : ℕ) : Type := {z : Mx D N r × Mx D N t // e • z.1 = z.1 ∧ e • z.2 = z.2}

def phiU (V : HSp D) (r t : ℕ) (h : GA D V) : (Mx D V.rank r × Mx D V.rank t) ≃ₜ (Mx D V.rank r × Mx D V.rank t) where
  toFun z := (mm (mt V h) z.1, mm (mt V h) z.2)
  invFun z := (mm (mt V h⁻¹) z.1, mm (mt V h⁻¹) z.2)
  left_inv z := by
    have e₁ : mt V h⁻¹ * mt V h = 1 := by
      simp only [Formalism.L2.Theta.mt]
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    refine Prod.ext ?_ ?_
    · change (mt V h⁻¹ * (mt V h * z.1 : Matrix _ _ _) : Matrix _ _ _) = z.1
      rw [← Matrix.mul_assoc, e₁, Matrix.one_mul]
    · change (mt V h⁻¹ * (mt V h * z.2 : Matrix _ _ _) : Matrix _ _ _) = z.2
      rw [← Matrix.mul_assoc, e₁, Matrix.one_mul]
  right_inv z := by
    have e₁ : mt V h * mt V h⁻¹ = 1 := by
      simp only [Formalism.L2.Theta.mt]
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    refine Prod.ext ?_ ?_
    · change (mt V h * (mt V h⁻¹ * z.1 : Matrix _ _ _) : Matrix _ _ _) = z.1
      rw [← Matrix.mul_assoc, e₁, Matrix.one_mul]
    · change (mt V h * (mt V h⁻¹ * z.2 : Matrix _ _ _) : Matrix _ _ _) = z.2
      rw [← Matrix.mul_assoc, e₁, Matrix.one_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_fst).prodMk (continuous_const.matrix_mul continuous_snd)
  continuous_invFun := (continuous_const.matrix_mul continuous_fst).prodMk (continuous_const.matrix_mul continuous_snd)

def phiS (N : ℕ) (y : Mx D r t) : (Mx D N r × Mx D N t) ≃ₜ (Mx D N r × Mx D N t) where
  toFun z := (z.1, z.2 + mm z.1 y)
  invFun z := (z.1, z.2 + mm z.1 (-y))
  left_inv z := by simp [Matrix.mul_neg]
  right_inv z := by simp [Matrix.mul_neg]
  continuous_toFun := continuous_fst.prodMk (continuous_snd.add (continuous_fst.matrix_mul continuous_const))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.add (continuous_fst.matrix_mul continuous_const))

def phiG (N r : ℕ) (g : GL (Fin t) (AE D)) : (Mx D N r × Mx D N t) ≃ₜ (Mx D N r × Mx D N t) where
  toFun z := (z.1, mm z.2 g.1)
  invFun z := (z.1, mm z.2 (g⁻¹).1)
  left_inv z := by
    have e₁ : g.1 * (g⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine Prod.ext rfl ?_
    change ((z.2 * g.1 : Matrix _ _ _) * (g⁻¹).1 : Matrix _ _ _) = z.2
    rw [Matrix.mul_assoc, e₁, Matrix.mul_one]
  right_inv z := by
    have e₁ : (g⁻¹).1 * g.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    refine Prod.ext rfl ?_
    change ((z.2 * (g⁻¹).1 : Matrix _ _ _) * g.1 : Matrix _ _ _) = z.2
    rw [Matrix.mul_assoc, e₁, Matrix.mul_one]
  continuous_toFun := continuous_fst.prodMk (continuous_snd.matrix_mul continuous_const)
  continuous_invFun := continuous_fst.prodMk (continuous_snd.matrix_mul continuous_const)

end GlobalTheory.CompanionTheory.EisM

namespace GlobalTheory.CompanionTheory.EisM
variable {D : D7} {N r t n : ℕ}

def liftU {e : AE D} (V : HSp D) (r t : ℕ) (h : GA D V) : XS e V.rank r t ≃ₜ XS e V.rank r t :=
  (phiU V r t h).subtype (fun z => by
    have a : ∀ {k : ℕ} (x : Mx D V.rank k), e • mm (mt V h) x = mm (mt V h) (e • x) := fun x => (Matrix.mul_smul _ _ _).symm
    have b : ∀ {k : ℕ} (x : Mx D V.rank k), e • mm (mt V h) x = mm (mt V h) x → e • x = x := fun {k} x hx => by
      have i := congrArg (fun y => mm (mt V h⁻¹) y) hx
      have l : ∀ y : Mx D V.rank k, mm (mt V h⁻¹) (mm (mt V h) y) = y := fun y =>
        congrArg Prod.fst ((phiU V k k h).left_inv (y, y))
      simpa only [a, l] using i
    refine ⟨fun hz => ⟨?_, ?_⟩, fun hz => ⟨b _ hz.1, b _ hz.2⟩⟩
    · change e • mm (mt V h) z.1 = mm (mt V h) z.1
      rw [a, hz.1]
    · change e • mm (mt V h) z.2 = mm (mt V h) z.2
      rw [a, hz.2])

def liftS {e : AE D} (N : ℕ) (y : Mx D r t) : XS e N r t ≃ₜ XS e N r t :=
  (phiS N y).subtype (fun z => by
    have a : ∀ x : Mx D N r, e • x = x → e • mm x y = mm x y := fun x hx => by
      simp only [mm]
      rw [← Matrix.smul_mul, hx]
    refine ⟨fun hz => ⟨hz.1, ?_⟩, fun hz => ⟨hz.1, ?_⟩⟩
    · change e • (z.2 + mm z.1 y) = z.2 + mm z.1 y
      rw [smul_add, hz.2, a _ hz.1]
    · have h₂ : e • (z.2 + mm z.1 y) = z.2 + mm z.1 y := hz.2
      have h₁ : e • z.1 = z.1 := hz.1
      rw [smul_add, a _ h₁] at h₂
      exact add_right_cancel h₂)

def liftG {e : AE D} (N r : ℕ) (g : GL (Fin t) (AE D)) : XS e N r t ≃ₜ XS e N r t :=
  (phiG N r g).subtype (fun z => by
    have a : ∀ x : Mx D N t, e • mm x g.1 = mm (e • x) g.1 := fun x => (Matrix.smul_mul _ _ _).symm
    refine ⟨fun hz => ⟨hz.1, ?_⟩, fun hz => ⟨hz.1, ?_⟩⟩
    · change e • mm z.2 g.1 = mm z.2 g.1
      rw [a, hz.2]
    · have h₂ : e • mm z.2 g.1 = mm z.2 g.1 := hz.2
      have i := congrArg (fun y => mm y (g⁻¹).1) h₂
      have l : ∀ y : Mx D N t, mm (mm y g.1) (g⁻¹).1 = y := fun y =>
        congrArg Prod.snd ((phiG N r g).left_inv ((0 : Mx D N r), y))
      simpa only [a, l] using i)

end GlobalTheory.CompanionTheory.EisM
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbEx

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
open IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.OrbExist


set_option maxHeartbeats 1600000 in
theorem orbEx : IdemEx → ApproxId → Dens → TopX → AlgRich → AlgStab → SigLaw → HermScale → OrbEx := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro _hIE hAI hDens hTop hAR hAS hSL hHS D n r t hn V hV ψ hψ θ hθ b₀ hb S e hS he fib μt hfib hfibs
      hfibi hμt lam hlam hIntg
    obtain ⟨i1, i2, i3, i4, i5, hemb, i7, i8, i9⟩ := hTop D V.rank r t e
    have hT2 : ∀ a b : ℕ, T2Space (Formalism.IndefR.Datum.Mx D a b) := by
      intro a b
      obtain ⟨j1, -, -, -, -, -, -, -, -⟩ := hTop D a 0 b 1
      let f : Formalism.IndefR.Datum.Mx D a b → PositivityTheory.Rg.Rsw.Em.XS D a 0 b 1 :=
        fun x => ⟨((0 : Formalism.IndefR.Datum.Mx D a 0), x), one_smul _ _, one_smul _ _⟩
      have hf : Continuous f := (continuous_const.prodMk continuous_id).subtype_mk _
      constructor
      intro x y hxy
      obtain ⟨U, W, hU, hW, hxU, hyW, hUW⟩ := t2_separation (x := f x) (y := f y)
        (fun h => hxy (congrArg (fun w => (Subtype.val w).2) h))
      exact ⟨f ⁻¹' U, f ⁻¹' W, hU.preimage hf, hW.preimage hf, hxU, hyW, hUW.preimage f⟩
    haveI := hT2 t t
    haveI := hT2 r r
    obtain ⟨hσfin, hσY, -, hσU, hσS, hσG⟩ :=
      hSL D r t V b₀ S e hS he fib μt hfib hfibs hfibi hμt
    obtain ⟨gk, Gk, hgG, htend, hdec⟩ := hAI D t ψ hψ S e hS lam hlam
    have hRich := hAR D θ hθ V.rank r t n hn S e hS
    let k : ↥(PositivityTheory.Rg.Rsw.L.hermS D t e) → PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e → ℂ :=
      fun x z => PositivityTheory.Rg.Rsw.L.pch ψ (Subtype.val (Subtype.val x))
        (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z))
    have hkc : Continuous (fun p : ↥(PositivityTheory.Rg.Rsw.L.hermS D t e) × PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e =>
        PositivityTheory.Rg.Rsw.L.pch ψ (Subtype.val (Subtype.val p.1)) (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val p.2))) :=
      GlobalTheory.CompanionTheory.OrbExist.continuous_pch₂ hψ
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))
        ((GlobalTheory.CompanionTheory.OrbExist.continuous_qv V b₀).comp (continuous_subtype_val.comp continuous_snd))
    have hD := hDens (PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e) (↥(PositivityTheory.Rg.Rsw.L.hermS D t e))
      (PositivityTheory.Rg.Rsw.Em.sig S he (fib.prod μt)) lam k (PositivityTheory.Rg.Rsw.Em.algA θ hn S e)
      {z | PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z) = 0}
      {z | PositivityTheory.Rg.Rsw.L.ip V (Subtype.val z).1 (Subtype.val z).1 = e • GlobalTheory.MixModel.rat (Subtype.val b₀)}
      gk (fun j z => Gk j (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z)))
      hσfin hkc.measurable (fun x z => (hψ.2.1 _).le) hRich.1
      (isClosed_eq ((GlobalTheory.CompanionTheory.OrbExist.continuous_qv V b₀).comp continuous_subtype_val) continuous_const)
      (isClosed_eq ((GlobalTheory.CompanionTheory.OrbExist.continuous_ip_fst (r := r) (t := t) V).comp continuous_subtype_val)
        continuous_const)
      hσY
      (fun j => ⟨(hgG j).1, (hgG j).2.1, fun z _ => (hgG j).2.2 _ (GlobalTheory.CompanionTheory.OrbExist.qv_mem V b₀ _)⟩)
      htend
      (fun C hC _ hCZ ε hε => by
        have hC' : IsCompact ((fun z : PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e =>
            PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z)) '' C) :=
          hC.image ((GlobalTheory.CompanionTheory.OrbExist.continuous_qv V b₀).comp continuous_subtype_val)
        filter_upwards [hdec _ hC'.isClosed (by
          rintro _ ⟨z, hz, rfl⟩
          exact ⟨GlobalTheory.CompanionTheory.OrbExist.qv_mem V b₀ _, GlobalTheory.CompanionTheory.OrbExist.qv_smul V b₀ e _ z.2.2,
            fun h0 => Set.disjoint_left.1 hCZ hz h0⟩) ε hε] with j hj z hz
        exact hj _ ⟨z, hz, rfl⟩)
      hIntg
    obtain ⟨ν, hνfin, hνsupp, hνint, hνcov⟩ := hD
    have hYae : ∀ᵐ z ∂(PositivityTheory.Rg.Rsw.Em.sig S he (fib.prod μt)),
        PositivityTheory.Rg.Rsw.L.ip V (Subtype.val z).1 (Subtype.val z).1 = e • GlobalTheory.MixModel.rat (Subtype.val b₀) :=
      MeasureTheory.ae_iff.2 hσY
    refine ⟨ν, ⟨?_, ?_, ?_, ?_, ?_⟩, hνint⟩
    · refine ⟨fun K hK => ?_⟩
      rw [hemb.map_apply]
      exact hνfin.lt_top_of_isCompact
        ((GlobalTheory.CompanionTheory.OrbExist.isClosed_fixed (a := V.rank) (r := r) (t := t)
          e).isClosedEmbedding_subtypeVal.isCompact_preimage hK)
    · rw [hemb.map_apply]
      refine measure_mono_null ?_ hνsupp
      intro z hz hYZ
      exact hz ⟨z.2.1, z.2.2, hYZ.1, hYZ.2⟩
    · intro h hh
      let Θ : PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e ≃ₜ PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e :=
        GlobalTheory.CompanionTheory.EisM.liftU V r t h
      have hcov : MeasureTheory.Measure.map Θ ν = (1 : NNReal) • ν := by
        refine hνcov Θ 1 fun f hf => ⟨?_, ?_⟩
        · refine GlobalTheory.CompanionTheory.OrbExist.comp_mem hθ hS hRich.2 hAS (Formalism.L2.Theta.matHom V h) 1 hh (by simp) Θ
            (fun z => ?_) f hf
          rw [GlobalTheory.CompanionTheory.OrbExist.mm_jn, Units.val_one]
          exact (Matrix.mul_one _).symm
        · exact GlobalTheory.CompanionTheory.OrbExist.trans_int₁ _ lam k f Θ (hσU h hh Θ fun z => rfl) fun x =>
            Filter.Eventually.of_forall fun z => by
              show PositivityTheory.Rg.Rsw.L.pch ψ _ (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z)) =
                PositivityTheory.Rg.Rsw.L.pch ψ _ (PositivityTheory.Rg.Rsw.L.qv V b₀
                  (PositivityTheory.Rg.Rsw.L.mm (Formalism.L2.Theta.mt V h) (Subtype.val z).1,
                    PositivityTheory.Rg.Rsw.L.mm (Formalism.L2.Theta.mt V h) (Subtype.val z).2))
              simp only [PositivityTheory.Rg.Rsw.L.qv, PositivityTheory.Rg.Rsw.L.yv, GlobalTheory.CompanionTheory.ColumnSplitting.GramAct.ip_mt]
      have := GlobalTheory.CompanionTheory.OrbExist.map_val_rel ν Subtype.val Θ (GlobalTheory.CompanionTheory.EisM.phiU V r t h) 1 hemb.measurable
        Θ.continuous.measurable (GlobalTheory.CompanionTheory.EisM.phiU V r t h).continuous.measurable (fun z => rfl) hcov
      rw [one_smul] at this
      exact this
    · intro y hy
      let Θ : PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e ≃ₜ PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e :=
        GlobalTheory.CompanionTheory.EisM.liftS V.rank y
      have hcov : MeasureTheory.Measure.map Θ ν = (1 : NNReal) • ν := by
        refine hνcov Θ 1 fun f hf => ⟨?_, ?_⟩
        · refine GlobalTheory.CompanionTheory.OrbExist.comp_mem hθ hS hRich.2 hAS 1 (GlobalTheory.CompanionTheory.OrbExist.shU hn y) (by simp)
            (GlobalTheory.CompanionTheory.OrbExist.smul_blockMatrix_sub_one hn e 1 y 0 1 (by simp) hy (by simp) (by simp)) Θ
            (fun z => ?_) f hf
          rw [Units.val_one, show ∀ X : Matrix (Fin V.rank) (Fin n) (Formalism.L2.Theta.AE D),
            PositivityTheory.Rg.Rsw.L.mm (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D)) X = X from
            fun X => Matrix.one_mul X]
          refine Eq.trans ?_ (GlobalTheory.CompanionTheory.ColumnSplitting.jnBl D n t V.rank r hn (Subtype.val z).1 (Subtype.val z).2 y).symm
          show PositivityTheory.Rg.Rsw.L.jn hn (Subtype.val z).1
            ((Subtype.val z).2 + PositivityTheory.Rg.Rsw.L.mm (Subtype.val z).1 y) = _
          rw [add_comm]
        · exact GlobalTheory.CompanionTheory.OrbExist.trans_int₁ _ lam k f Θ (hσS y hy Θ fun z => rfl) fun x =>
            hYae.mono fun z hz => by
              show PositivityTheory.Rg.Rsw.L.pch ψ _ (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z)) =
                PositivityTheory.Rg.Rsw.L.pch ψ _ (PositivityTheory.Rg.Rsw.L.qv V b₀
                  ((Subtype.val z).1, (Subtype.val z).2 + PositivityTheory.Rg.Rsw.L.mm (Subtype.val z).1 y))
              rw [GlobalTheory.CompanionTheory.OrbExist.qv_shear V b₀ hb e _ _ y hz hy]
      have := GlobalTheory.CompanionTheory.OrbExist.map_val_rel ν Subtype.val Θ (GlobalTheory.CompanionTheory.EisM.phiS V.rank y) 1 hemb.measurable
        Θ.continuous.measurable (GlobalTheory.CompanionTheory.EisM.phiS V.rank y).continuous.measurable (fun z => rfl) hcov
      rw [one_smul] at this
      exact this
    · intro g hg
      let Θ : PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e ≃ₜ PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e :=
        GlobalTheory.CompanionTheory.EisM.liftG V.rank r g
      obtain ⟨c, hc, hcmap⟩ := hHS D t S e hS lam hlam g⁻¹ (GlobalTheory.CompanionTheory.OrbExist.smul_inv_sub e g hg)
      have hκ : ((GlobalTheory.Doubling.absA D) (Matrix.GeneralLinearGroup.det g))⁻¹ ^ V.rank *
          ((GlobalTheory.Doubling.absA D) (Matrix.GeneralLinearGroup.det g⁻¹))⁻¹ ^ t =
          ((GlobalTheory.Doubling.absA D) (Matrix.GeneralLinearGroup.det g))⁻¹ ^ (r + t) := by
        rw [map_inv, GlobalTheory.CompanionTheory.OrbExist.absA_inv]
        exact GlobalTheory.CompanionTheory.OrbExist.kap _ (GlobalTheory.CompanionTheory.OrbExist.absA_ne D _) V.rank r t hV
      have hkG : ∀ x, ∀ᵐ z ∂(PositivityTheory.Rg.Rsw.Em.sig S he (fib.prod μt)), k x z = k (c x) (Θ z) :=
        fun x => Filter.Eventually.of_forall fun z => by
          show PositivityTheory.Rg.Rsw.L.pch ψ (Subtype.val (Subtype.val x)) (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z)) =
            PositivityTheory.Rg.Rsw.L.pch ψ (Subtype.val (Subtype.val (c x))) (PositivityTheory.Rg.Rsw.L.qv V b₀
              ((Subtype.val z).1, PositivityTheory.Rg.Rsw.L.mm (Subtype.val z).2
                (g : Matrix (Fin t) (Fin t) (Formalism.L2.Theta.AE D))))
          rw [hc x, ← GlobalTheory.CompanionTheory.OrbExist.pch_conj, GlobalTheory.CompanionTheory.OrbExist.qv_col, GlobalTheory.CompanionTheory.OrbExist.conj_cancel]
      have hcov : MeasureTheory.Measure.map Θ ν =
          ((GlobalTheory.Doubling.absA D) (Matrix.GeneralLinearGroup.det g))⁻¹ ^ (r + t) • ν := by
        refine hνcov Θ _ fun f hf => ⟨?_, ?_⟩
        · refine GlobalTheory.CompanionTheory.OrbExist.comp_mem hθ hS hRich.2 hAS 1 (GlobalTheory.CompanionTheory.OrbExist.colU hn g) (by simp)
            (GlobalTheory.CompanionTheory.OrbExist.smul_blockMatrix_sub_one hn e 1 0 0 (g : Matrix (Fin t) (Fin t) (Formalism.L2.Theta.AE D))
              (by simp) (by simp) (by simp) hg) Θ (fun z => ?_) f hf
          rw [Units.val_one, show ∀ X : Matrix (Fin V.rank) (Fin n) (Formalism.L2.Theta.AE D),
            PositivityTheory.Rg.Rsw.L.mm (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D)) X = X from
            fun X => Matrix.one_mul X]
          refine Eq.trans ?_ (GlobalTheory.CompanionTheory.OrbExist.jn_bl hn (Subtype.val z).1 (Subtype.val z).2 1 0 0
            (g : Matrix (Fin t) (Fin t) (Formalism.L2.Theta.AE D))).symm
          show PositivityTheory.Rg.Rsw.L.jn hn (Subtype.val z).1 (PositivityTheory.Rg.Rsw.L.mm (Subtype.val z).2
            (g : Matrix (Fin t) (Fin t) (Formalism.L2.Theta.AE D))) = _
          simp only [PositivityTheory.Rg.Rsw.L.mm, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add]
        · rw [GlobalTheory.CompanionTheory.OrbExist.trans_int _ lam k f Θ c _ _ (hσG g hg Θ fun z => rfl) hcmap hkG, hκ]
      exact GlobalTheory.CompanionTheory.OrbExist.map_val_rel ν Subtype.val Θ (GlobalTheory.CompanionTheory.EisM.phiG V.rank r g) _ hemb.measurable
        Θ.continuous.measurable (GlobalTheory.CompanionTheory.EisM.phiG V.rank r g).continuous.measurable (fun z => rfl) hcov

end GlobalTheory.CompanionTheory.OrbExist

end
end
end
