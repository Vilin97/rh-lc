module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaAtEqProdAhG
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitLinearModelNorm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCHLat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Basify
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryComponentFrameMarkingUniformisation
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AtPlaceIffEqAtTau
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangular
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalMapColumnsMemLatGIffMovedFinitePart

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section




namespace GlobalTheory.ColSplit

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues GlobalTheory.AdLat
open scoped TensorProduct

variable {D : D7}

theorem finite_part_apply (V W : HSp D) (Y : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (i : Fin W.rank) (j : Fin V.rank) :
    (ratW W V Y - realPt V W Y : WO V W) i j = (pairA D.host.F 0 1) ⊗ₜ[D.host.F] Y i j := by
  change (1 : AF D.host.F) ⊗ₜ[D.host.F] Y i j - (pairA D.host.F 1 0) ⊗ₜ[D.host.F] Y i j = _
  rw [← TensorProduct.sub_tmul]
  congr 1
  exact Prod.ext (sub_self (1 : Ainf D.host.F)) (sub_zero (1 : Af D.host.F))

def rk (V W : HSp D) (s : Fin V.rank → D.host.E) : (Fin W.rank → D.host.E) →+ WO V W where
  toFun c := Matrix.of fun i j => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (c i * ∑ k, star (s k) * V.gram k j)
  map_zero' := by ext i j; simp
  map_add' y z := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, add_mul, TensorProduct.tmul_add]

theorem rk_mem (V W : HSp D) (LV : Set (Fin V.rank → D.host.E)) (L : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E))
    (s : Fin V.rank → D.host.E) (hs : s ∈ LV) (c : Fin W.rank → D.host.E)
    (hc : c ∈ Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ L, w = a • v}) :
    rk V W s c ∈ latO V W LV (L : Set (Fin W.rank → D.host.E)) fun _ => True := by
  have hc' := (GlobalTheory.OneMapRef.FactsLat.isAA_span L c).1 hc
  clear hc
  induction hc' using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, t, ht, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨1, fun _ => one_mem _, fun _ h => absurd trivial h, a, ha, s, hs, t, ht, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

def colF (V W : HSp D) (s : Fin V.rank → D.host.E) : WO V W →+ (Fin W.rank → RA D.host.F D.host.E) where
  toFun u := fun m => ∑ n, finPart D (u m n) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] s n)
  map_zero' := by ext m; simp
  map_add' y z := by
    ext m
    simp only [Matrix.add_apply, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem colF_pure (V W : HSp D) (s : Fin V.rank → D.host.E) (α : Af D.host.F)
    (X : Matrix (Fin W.rank) (Fin V.rank) D.host.E) :
    colF V W s (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] X i j) =
      fun m => α ⊗ₜ[D.host.F] ∑ n, X m n * s n := by
  funext m
  change ∑ n, (α ⊗ₜ[D.host.F] X m n) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] s n) = _
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, TensorProduct.tmul_sum]

theorem colF_mem (V W : HSp D) (L : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E))
    (s : Fin V.rank → D.host.E) (hs : s ∈ GlobalTheory.Member.latC V) (u : WO V W)
    (hu : u ∈ latO V W (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) (L : Set (Fin W.rank → D.host.E)) fun _ => True) :
    colF V W s u ∈ hat D.host.F ((Submodule.span (𝓞 D.host.E)
      {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ L, w = a • v} : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) :
        Set (Fin W.rank → D.host.E)) := by
  induction hu using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, -, a, ha, s', hs', t, ht, rfl⟩ := hx
    rw [colF_pure V W s α fun i j => a * t i * ∑ k, star (s' k) * V.gram k j]
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1
      (((GlobalTheory.Member.latHat_eq_hat_and_gram D V).2.2.2.2.2.2.2.2.2.2 s).2 hs s' hs')
    refine AddSubgroup.subset_closure ⟨α, hα, a • (r • t), Submodule.subset_span ⟨a, ha, _, L.smul_mem r ht, rfl⟩, ?_⟩
    funext m
    congr 1
    change _ = a * (algebraMap (𝓞 D.host.E) D.host.E r * t m)
    rw [hr]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun k _ => ?_
    change _ = a * (s n * V.gram k n * star (s' k) * t m)
    ring
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem complete (V : HSp D) (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hb : IsONLatBasis V b) (n j : Fin V.rank) :
    ∑ a, b n a * ∑ k, star (b k a) * V.gram k j = if n = j then 1 else 0 := by
  have h1 : (Matrix.of fun a j => ∑ k, star (b k a) * V.gram k j) * b = 1 := by
    ext a a'
    rw [Matrix.one_apply, ← hb.1 a a', Matrix.mul_apply, Finset.sum_comm]
    simp only [Matrix.of_apply, Finset.sum_mul]
  have h3 : b * (Matrix.of fun a j => ∑ k, star (b k a) * V.gram k j) = 1 := mul_eq_one_comm.1 h1
  have h2 := congrFun (congrFun h3 n) j
  rw [Matrix.one_apply, Matrix.mul_apply] at h2
  exact h2

theorem cols_iff_moved (V W : HSp D) (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hb : IsONLatBasis V b) (y : GA D W)
    (Y : Matrix (Fin W.rank) (Fin V.rank) D.host.E) :
    (∀ a, (fun m => ∑ n, Y m n * b n a) ∈ latG W y) ↔
      (ratW W V Y - realPt V W Y : WO V W) ∈ latO V W (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
        (Bridge.hLat W (FWT.fin W y) : Set (Fin W.rank → D.host.E)) fun _ => True := by
  have hbm : ∀ a, (fun i => b i a) ∈ GlobalTheory.Member.latC V := fun a => by
    rw [← SetLike.mem_coe, GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq, hb.2]
    exact Submodule.subset_span ⟨a, rfl⟩
  constructor
  · intro h
    have e : (ratW W V Y - realPt V W Y : WO V W) = ∑ a, rk V W (fun i => b i a) fun m => ∑ n, Y m n * b n a := by
      ext i j
      rw [finite_part_apply, Matrix.sum_apply]
      change _ = ∑ a, (pairA D.host.F 0 1) ⊗ₜ[D.host.F] ((∑ n, Y i n * b n a) * ∑ k, star (b k a) * V.gram k j)
      rw [← TensorProduct.tmul_sum]
      congr 1
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [mul_assoc, ← Finset.mul_sum, complete V b hb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
    rw [e]
    refine sum_mem fun a _ => rk_mem V W _ _ _ (hbm a) _ ?_
    rw [← GlobalTheory.MovedLat.latG_eq]
    exact h a
  · intro h a
    have h1 := colF_mem V W _ _ (hbm a) _ h
    rw [← GlobalTheory.MovedLat.latG_eq] at h1
    have e : (ratW W V Y - realPt V W Y : WO V W) =
        Matrix.of fun i j => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] Y i j := by
      ext i j; exact finite_part_apply V W Y i j
    rw [e, colF_pure] at h1
    obtain ⟨f1, f2, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D W y
    exact ((hat_rational_points_and_approx D.host.F D.host.E W.rank _ f1 f2).1 _).1 h1

theorem moved_iff (V W : HSp D) (y : GA D W) (u : WO V W) :
    u ∈ (latO V W (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
        (Bridge.hLat W (FWT.fin W y) : Set (Fin W.rank → D.host.E)) fun _ => True) ↔
      actO V W 1 y⁻¹ u ∈ latO V W (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
        (GlobalTheory.Member.latC W : Set (Fin W.rank → D.host.E)) fun _ => True := by
  have h1 : ∀ z ∈ hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)),
      Matrix.mulVec (finHom V 1).1 z ∈ hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
    intro z hz
    rw [map_one, Units.val_one, Matrix.one_mulVec]
    exact hz
  constructor
  · exact GlobalTheory.MovedLat.actO_mem V W 1 y⁻¹ _ _ _ _ h1 (GlobalTheory.MovedLat.bwd W y) u
  · intro h
    have h2 := GlobalTheory.MovedLat.actO_mem V W 1 y _ _ _ _ h1 (GlobalTheory.MovedLat.fwd W y) _ h
    have h3 := GlobalTheory.AdelicLatMove.actO_actO_inv V W 1 y u
    rw [inv_one] at h3
    rwa [h3] at h2

theorem cols_mem_iff : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E),
    GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis (Vc D i) b → ∀ (y : GA D (Wc D i)) (Yr : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E),
      (∀ a, (fun m => ∑ n, Yr m n * b n a) ∈ latG (Wc D i) y) ↔
        actO (Vc D i) (Wc D i) 1 y⁻¹ (ratW (Wc D i) (Vc D i) Yr - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) Yr) ∈
          latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hR i b hb y Yr
  have hV := (GlobalTheory.OneMapRef.FactsLat.selfDual_frame_level_one_lattice_eq_standard (hR.βV i)).trans (GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq _).symm
  have hW := (GlobalTheory.OneMapRef.FactsLat.selfDual_frame_level_one_lattice_eq_standard (hR.βW i)).trans (GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq _).symm
  rw [cols_iff_moved _ _ b hb, moved_iff, ← hV, ← hW]

end GlobalTheory.ColSplit
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalMapColumnsMemLatGIffMovedFinitePartStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section


theorem _root_.GlobalTheory.T.rationalMap_columns_mem_latG_iff_moved_finitePart : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E),
    GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis (Vc D i) b → ∀ (y : GA D (Wc D i)) (Yr : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E),
      (∀ a, (fun m => ∑ n, Yr m n * b n a) ∈ latG (Wc D i) y) ↔
        actO (Vc D i) (Wc D i) 1 y⁻¹ (ratW (Wc D i) (Vc D i) Yr - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) Yr) ∈
          latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True := by
  first | exact @GlobalTheory.ColSplit.cols_mem_iff | exact GlobalTheory.ColSplit.cols_mem_iff | (intros; apply GlobalTheory.ColSplit.cols_mem_iff <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaDictionaryLatticeOfFrameCoordinates

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
noncomputable section

namespace GlobalTheory.DictLatPin

variable {D : D7}

theorem latFrame_cast {V W : HSp D} (hV : V = W) {r : ℕ} (hr : V.rank = r) (hr' : W.rank = r)
    {Comp : Type} {X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r}
    (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r)
    (th : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (h : ∀ h : GA D V, ∃ γ ∈ GQ V,
      ((X (dict h).1).Λ : Set (Fin r → D.host.E)) =
        (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ * h) : Set _) ∧
      ∀ τ : (X (dict h).1).Ψ, ReciprocityTheory.ChartRestriction.G.FD.mat (dict h).2 τ =
        Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th (dict h).1 τ) (γ * h)) * x₀ τ.1)
    (g : GA D W) : ∃ γ ∈ GQ W,
      ((X (castDict hV dict g).1).Λ : Set (Fin r → D.host.E)) =
        (fun v : Fin W.rank → D.host.E => v ∘ Fin.cast hr'.symm) '' (latG W (γ * g) : Set _) ∧
      ∀ τ : (X (castDict hV dict g).1).Ψ, ReciprocityTheory.ChartRestriction.G.FD.mat (castDict hV dict g).2 τ =
        Matrix.reindex (finCongr hr') (finCongr hr') (archM W (th (castDict hV dict g).1 τ) (γ * g)) * x₀ τ.1 := by
  subst hV
  exact h g

end GlobalTheory.DictLatPin


open GlobalTheory.DictLatPin in

theorem GlobalTheory.DictLatPin.lat_of_frAt : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i),
    ∀ γ ∈ GQ (Wc D i), ∀ (g : GA D (Wc D i)),
      FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ g →
    ∀ v : Fin D.R.r → D.host.E,
      v ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV g).1).Λ ↔
        (fun m => v (Fin.cast (rank_Wc i) m)) ∈ latG (Wc D i) (γ * g) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ _ _ hMods _ hT i σ hσ hV γ hγ g hFr v
  subst hσ
  have hj : InR D ((i : ℕ) + 1) := inR i
  have hL := hT.laws
  have hg := T.toCore.good_σ₀
  have hP := hL.pins
  obtain ⟨hr, g', e, F', ik, φ, th, -, -, hth, hD⟩ := hL.adPin _ hj _ hg
  have hcl := latFrame_cast hV hr (rank_Wc i) (T.dict ((i : ℕ) + 1) T.σ₀) th (T.x₀ ((i : ℕ) + 1) T.σ₀)
    (fun h => by
      obtain ⟨γ₁, hq, hl, -, hf⟩ := hD.2 h
      exact ⟨γ₁, hq, hl, hf⟩) g
  obtain ⟨γ', hγ', hΛ, hf'⟩ := hcl

  have hres : res T (sg0 D A) = T.toCore.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0, res_embLL T hT.alg hP.2.2.1]
  have hx : IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.toCore.σ₀) :=
    hres ▸ hT.x0 i (sg0 D A) (base_embedding_good T R hT.alg hP.2.2.1)
  set k := (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i T.σ₀ hV g).1 with hk
  have hU := hL.unf _ hj _ hg
  have hΨ := (hU.2.1 k).2
  obtain ⟨ρ₀⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hτ₀ : tauE D ρ₀ ∈ ((T.U ((i : ℕ) + 1) T.σ₀).X k).Ψ := (hΨ _).2 (hP.1.2.2.2 ρ₀)
  let τ₀ : ((T.U ((i : ℕ) + 1) T.σ₀).X k).Ψ := ⟨tauE D ρ₀, hτ₀⟩
  have h1 := hFr ρ₀ τ₀ rfl
  have h2 := hf' τ₀
  have hth' : th k τ₀ = R.θ ρ₀ := GlobalTheory.LettersCheck.isInfEmb_unique (tauE D ρ₀) _ _ (hth k τ₀) (hMods.inf ρ₀)
  rw [← hx.mul] at h1
  rw [hth'] at h2
  have h3 : Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i)) (archM (Wc D i) (R.θ ρ₀) (γ' * g)) *
      T.x₀ ((i : ℕ) + 1) T.σ₀ (tauE D ρ₀) =
      Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i)) (archM (Wc D i) (R.θ ρ₀) (γ * g)) *
      T.x₀ ((i : ℕ) + 1) T.σ₀ (tauE D ρ₀) := h2.symm.trans h1
  have hx₀ : IsOrthogonalFrame ((T.U ((i : ℕ) + 1) T.σ₀).X k) (T.x₀ ((i : ℕ) + 1) T.σ₀) := hL.familyUniformisationBasePointOrthogonal _ hj _ hg k
  obtain ⟨-, hu2, -⟩ := GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E D.R.r
    ((T.U ((i : ℕ) + 1) T.σ₀).X k).p0 ((T.U ((i : ℕ) + 1) T.σ₀).X k).Ψ ((T.U ((i : ℕ) + 1) T.σ₀).X k).Gm
    ((T.U ((i : ℕ) + 1) T.σ₀).X k).Gm_herm
  have hdet : IsUnit (T.x₀ ((i : ℕ) + 1) T.σ₀ (tauE D ρ₀)).det :=
    (((hu2 (fun τ => T.x₀ ((i : ℕ) + 1) T.σ₀ τ.1) fun τ => hx₀ τ.1 τ.2).1 τ₀).1).isUnit
  have h4 : archM (Wc D i) (R.θ ρ₀) (γ' * g) = archM (Wc D i) (R.θ ρ₀) (γ * g) := by
    have := congrArg (· * (T.x₀ ((i : ℕ) + 1) T.σ₀ (tauE D ρ₀))⁻¹) h3
    simp only [Matrix.mul_nonsing_inv_cancel_right _ _ hdet] at this
    exact (Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i))).injective this
  have h5 : ∀ δ : GA D (Wc D i), archM (Wc D i) (R.θ ρ₀) δ =
      archM (Wc D i) (R.θ ρ₀) (δ * g) * archM (Wc D i) (R.θ ρ₀) g⁻¹ := fun δ => by
    rw [← GlobalTheory.PointAtPlace.archM_mul, mul_inv_cancel_right]
  have hγγ : γ' = γ := GlobalTheory.AdTh.MarkUniq.rat_eq_of_archM (Wc D i) hγ' hγ (tauE D ρ₀) (R.θ ρ₀) (hMods.inf ρ₀)
    (by rw [h5 γ', h5 γ, h4])
  subst hγγ
  rw [← SetLike.mem_coe, hΛ]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : w ∈ latG (Wc D i) (γ' * g) := hw
    convert hw' using 1
    funext m
    simp
  · intro hv
    exact ⟨_, hv, funext fun m => by simp⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaDictionaryLatticeOfFrameCoordinatesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section


theorem _root_.GlobalTheory.T.thetaDictionary_lattice_of_frameCoordinates : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i),
    ∀ γ ∈ GQ (Wc D i), ∀ (g : GA D (Wc D i)),
      FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ g →
    ∀ v : Fin D.R.r → D.host.E,
      v ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV g).1).Λ ↔
        (fun m => v (Fin.cast (rank_Wc i) m)) ∈ latG (Wc D i) (γ * g) := by
  first | exact @GlobalTheory.DictLatPin.lat_of_frAt | exact GlobalTheory.DictLatPin.lat_of_frAt | (intros; apply GlobalTheory.DictLatPin.lat_of_frAt <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnsMemPeriodLatticeIffFinitePartMovedLattice

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.AHPhase

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom}

theorem perVec_mem_range_iff (Wt : UnfAt U k x) (v : Fin r → D.host.E) :
    perVec Wt v ∈ Set.range Wt.Pm ↔ v ∈ (U.X k).Λ := by
  constructor
  · rintro ⟨a, ha⟩
    set w := v - (Wt.φ k a : Fin r → D.host.E) with hw
    have hpw : pv Wt w = 0 := by
      have e1 : pv Wt w = pv Wt v - pv Wt (Wt.φ k a : Fin r → D.host.E) := map_sub (pvHom Wt) _ _
      rw [e1, pv_lat]
      change perVec Wt v - Wt.Pm a = 0
      rw [← ha, sub_self]
    obtain ⟨N, hN, hNw⟩ := exists_nsmul_mem (U.X k) w
    set c' := (Wt.φ k).symm ⟨N • w, hNw⟩ with hc'
    have hc : (Wt.φ k c' : Fin r → D.host.E) = (N : D.host.E) • w := by
      rw [hc', LinearEquiv.apply_symm_apply, Nat.cast_smul_eq_nsmul]
    have hP : Wt.Pm c' = Wt.Pm 0 := by
      rw [← pv_lat, hc, pv_nsmul, hpw, smul_zero, map_zero]
    have h0 : c' = 0 := Wt.per.2.1 hP
    have hw0 : (N : D.host.E) • w = 0 := by rw [← hc, h0, map_zero]; rfl
    have hw0' : w = 0 := by
      rcases smul_eq_zero.1 hw0 with h | h
      · exact absurd (Nat.cast_eq_zero.1 h) hN
      · exact h
    have : v = (Wt.φ k a : Fin r → D.host.E) := sub_eq_zero.1 hw0'
    rw [this]
    exact (Wt.φ k a).2
  · intro hv
    refine ⟨(Wt.φ k).symm ⟨v, hv⟩, ?_⟩
    rw [← perVec_lat, LinearEquiv.apply_symm_apply]

end GlobalTheory.AHPhase

theorem GlobalTheory.AHPhase.cols_per_iff_latO : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (ph : ℂ)
    (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E), ‖ph‖ = 1 → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis (Vc D i) b →
    ∀ γ ∈ GQ (Wc D i), ∀ (g : GA D (Wc D i)),
      FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ g →
    ∀ (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV g).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV g).1).dom)
      (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV g).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV g).2, hx⟩)
      (Y : UnitAt Wt), GlobalTheory.AHPhase.PinAt T R i σ hV ph b γ g hx Wt Y →
    ∀ Yr : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E,
      (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.perVec Wt (GlobalTheory.AHPhase.colB b Yr a) ∈ Set.range Wt.Pm) ↔
        actO (Vc D i) (Wc D i) 1 (γ * g)⁻¹ (ratW (Wc D i) (Vc D i) Yr - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) Yr) ∈
          latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True := by
  intro D hHk hSL hVF G _ _ Pl0 T0 A T _ R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV ph b hph hb γ hγ g hfr hx Wt Y hp Yr
  rw [← GlobalTheory.T.rationalMap_columns_mem_latG_iff_moved_finitePart D G Pl0 T0 A T.Q.c.F R hLev i b hb (γ * g) Yr]
  refine forall_congr' fun a => ?_
  rw [GlobalTheory.AHPhase.perVec_mem_range_iff,
    GlobalTheory.T.thetaDictionary_lattice_of_frameCoordinates D G Pl0 T0 A T R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV γ hγ g hfr]
  have e : (fun m : Fin (Wc D i).rank => GlobalTheory.AHPhase.colB b Yr a (Fin.cast (rank_Wc i) m)) =
      fun m => ∑ n, Yr m n * b n a := by
    funext m
    simp [GlobalTheory.AHPhase.colB]
  rw [e]
end
end
end
