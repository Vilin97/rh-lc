module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkFacStmt
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.FinSplit
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
import Development.WeilBound.ThetaLifts.LatticeBasics.PairsD
public import Development.WeilBound.ThetaLifts.LatticeBasics.RealInv
public import Development.WeilBound.ThetaLifts.SchwartzMoments.PolynomialFunctionalEvalContinuous
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PureEqPureA
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkFacArch
public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsB

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBasePairsL

section

@[expose] public section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Prs
open scoped TensorProduct Classical
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dens
open PositivityTheory.ThKF (ArchOp PureAct)
open PositivityTheory.ThK (LocRepEx)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ Y W} {o : Rep σ Y W} {R : RealMaps F a a'} {Rf : FinMaps F a a'}
  {p : SInf F (Fin n × Fin d) →ₗ[ℂ] R.Pi} {q : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] Rf.Pi v} {T T₁ : Finset (Pl F)}
theorem inf_op_k (hA : _root_.PositivityTheory.ThKF.ArchOp_k) {χ χ' r s r' s'} (hp : _root_.GlobalTheory.ThK.IsPair_k B M χ χ' o r s r' s') {k : UA σ W.J} (hk : k ∈ KInf σ W B.emb) :
    ∃ A : Module.End ℂ (SInf F (Fin n × Fin d)), ∀ f ∈ M.Pol B.ψ B.emb, A f ∈ M.Pol B.ψ B.emb ∧ Acts (evI F) (o (1, k)) f (A f) := by
  have o1 : (1 : UA σ Y.J) ∈ KInf σ Y B.emb :=
    ⟨fun u _ => by rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero], fun w => by
      rw [show mat (1 : UA σ Y.J) = 1 from rfl, Matrix.map_one _ (map_zero _) (map_one _)]; exact Commute.one_left _⟩
  obtain ⟨A, a1, a2⟩ := hA F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp 1 o1.1 k hk.1
  exact ⟨A, fun f hf => ⟨a2 o1 hk f hf, a1.2 f⟩⟩
variable {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
end GlobalTheory.ThK.Dbl.Prs
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBasePolFin

section

@[expose] public section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CompanionTheory.Ar.RT
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
theorem polFin_k {B : Base F E} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {χX χW} {om : Rep σ Y W} {r s r' s'}
    (h : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s') : ∀ f ∈ M.Pol B.ψ B.emb, ∃ U : Submodule ℂ (SInf F (Fin n × Fin d)),
      FiniteDimensional ℂ U ∧ ∀ k ∈ KInf σ W B.emb, ∀ f₁ : SInf F _, Acts (evI F) (om (1, k)) f f₁ → f₁ ∈ U := by
  intro f hf
  have hψ := h.base.std
  have hs := h.weil.isUSplitting.toIsSplitting
  let S : Submodule ℂ (SInf F (Fin n × Fin d)) :=
    { carrier := {f | ∃ U : Submodule ℂ (SInf F (Fin n × Fin d)), FiniteDimensional ℂ U ∧
        ∀ k ∈ KInf σ W B.emb, ∀ A, PositivityTheory.ThKOwn.KPol.Impl om k A → A f ∈ U}
      zero_mem' := ⟨⊥, inferInstance, fun k _ A _ => by rw [map_zero]; exact zero_mem _⟩
      add_mem' := by
        rintro f g ⟨N, _, h1⟩ ⟨N', _, h2⟩
        exact ⟨N ⊔ N', inferInstance, fun k hk A hA => by
          rw [map_add (f := _)]; exact Submodule.add_mem_sup (h1 k hk A hA) (h2 k hk A hA)⟩
      smul_mem' := fun c f ⟨N, h0, h1⟩ => ⟨N, h0, fun k hk A hA => by rw [map_smul]; exact N.smul_mem c (h1 k hk A hA)⟩ }
  obtain ⟨U, h0, h1⟩ : f ∈ S := by
    refine (sInf_le (a := S) ⟨fun f₀ h₀ => ?_, fun u hu g ⟨N, h0, h1⟩ g₁ hg => ?_⟩ : M.Pol B.ψ B.emb ≤ S) hf
    · haveI := Dense.vacSp_fin h.base.cm M B.emb
      refine ⟨⨆ ε, Dense.vacSp M B.emb ε, inferInstance, fun k hk A hA => ?_⟩
      have hgauss : M.IsGauss B.ψ B.emb (A f₀) := by
        obtain ⟨ε, hε⟩ := h₀
        refine ⟨ε, fun u u' hu hu' hrel f f' hf hf' => ?_⟩
        set N := (mat k⁻¹).transpose with hN
        have hNk : N * (mat k).transpose = 1 := by
          rw [hN, ← Matrix.transpose_mul, PositivityTheory.ThKOwn.KPol.mat_mul_inv, Matrix.transpose_one]
        have e1 : u * N * (mat k).transpose = u := by rw [Matrix.mul_assoc, hNk, Matrix.mul_one]
        have e2 : u' * N * (mat k).transpose = u' := by rw [Matrix.mul_assoc, hNk, Matrix.mul_one]
        have hf1 := PositivityTheory.ThKOwn.KPol.actsD_unique M hψ hu hf
        have hf2 := PositivityTheory.ThKOwn.KPol.actsD_unique M hψ hu' hf'
        have i1 := PositivityTheory.ThKOwn.KPol.inter hψ hs hA (PositivityTheory.ThKOwn.KPol.at_mul hu N) f₀
        have i2 := PositivityTheory.ThKOwn.KPol.inter hψ hs hA (PositivityTheory.ThKOwn.KPol.at_mul hu' N) f₀
        rw [e1, ← hf1] at i1
        rw [e2, ← hf2] at i2
        have hcomm : ∀ w, Commute ((mat k⁻¹).map (piInf (B.emb w))) (W.θ w) := fun w => by
          have hc : Commute ((mat k).map (piInf (B.emb w))) (W.θ w) := hk.2 w
          have h1 : (mat k⁻¹).map (piInf (B.emb w)) * (mat k).map (piInf (B.emb w)) = 1 := by
            rw [← Matrix.map_mul, PositivityTheory.ThKOwn.KPol.mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
          have h2 : (mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w)) = 1 := by
            rw [← Matrix.map_mul, PositivityTheory.ThKOwn.KPol.mat_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
          show _ * _ = _ * _
          calc (mat k⁻¹).map (piInf (B.emb w)) * W.θ w
              = (mat k⁻¹).map (piInf (B.emb w)) * W.θ w * ((mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w))) := by
                rw [h2, Matrix.mul_one]
            _ = (mat k⁻¹).map (piInf (B.emb w)) * (W.θ w * (mat k).map (piInf (B.emb w))) * (mat k⁻¹).map (piInf (B.emb w)) := by
                simp only [Matrix.mul_assoc]
            _ = (mat k⁻¹).map (piInf (B.emb w)) * ((mat k).map (piInf (B.emb w)) * W.θ w) * (mat k⁻¹).map (piInf (B.emb w)) := by
                rw [hc.eq]
            _ = W.θ w * (mat k⁻¹).map (piInf (B.emb w)) := by
                rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
        have hrel' : ∀ w, (u' * N).map (piInf (B.emb w)) =
            (((ε w : ℤ) : ℂ) * Complex.I) • (Y.θ w * (u * N).map (piInf (B.emb w)) * (W.θ w).transpose) := fun w => by
          have hN' : N.map (piInf (B.emb w)) = ((mat k⁻¹).map (piInf (B.emb w))).transpose := by
            rw [hN, Matrix.transpose_map]
          have hc : (W.θ w).transpose * N.map (piInf (B.emb w)) = N.map (piInf (B.emb w)) * (W.θ w).transpose := by
            rw [hN', ← Matrix.transpose_mul, ← Matrix.transpose_mul, (hcomm w).eq]
          rw [Matrix.map_mul, Matrix.map_mul, hrel w, Matrix.smul_mul]
          simp only [Matrix.mul_assoc, hc]
        have hg := hε (u * N) (u' * N) (PositivityTheory.ThKOwn.KPol.at_mul hu N) (PositivityTheory.ThKOwn.KPol.at_mul hu' N) hrel' _ _
          (PositivityTheory.ThKOwn.KPol.actsD_dop M hψ (PositivityTheory.ThKOwn.KPol.at_mul hu N) f₀) (PositivityTheory.ThKOwn.KPol.actsD_dop M hψ (PositivityTheory.ThKOwn.KPol.at_mul hu' N) f₀)
        rw [← i1, ← i2, hg, map_smul]
      obtain ⟨ε, hε⟩ := hgauss
      exact Submodule.mem_iSup_of_mem ε fun u u' hu hu' e => hε u u' hu hu' e _ _ (Dense.actsD_dop M hψ hu _)
        (Dense.actsD_dop M hψ hu' _)
    · obtain ⟨N', h3, h4⟩ := Dense.exists_dop_fin N
      refine ⟨N', h3, fun k hk A hA => ?_⟩
      rw [PositivityTheory.ThKOwn.KPol.actsD_unique M hψ hu hg, PositivityTheory.ThKOwn.KPol.inter hψ hs hA hu]
      exact h4 _ _ _ (h1 k hk A hA)
  refine ⟨U, h0, fun k hk f₁ h₁ => ?_⟩
  obtain ⟨A, hA⟩ := PositivityTheory.ThKOwn.KPol.exists_impl fun f => PositivityTheory.ThKOwn.KPol.exists_arch_operator hψ hs hk.1 f
  rw [PositivityTheory.ThKOwn.KPol.acts_unique hA h₁]
  exact h1 k hk A hA
end GlobalTheory.ThK.Dbl
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsFiniteDimensionalWeilArchimedeanOrbit

section

@[expose] public section



section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
open UpperTheory.TP
namespace UpperTheory.PolynomialDataFiniteKType₂
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
private theorem mat_inv_mul_pk {X : Spc F E n} (g : UA σ X.J) : mat g⁻¹ * mat g = 1 := by
  have : mat (g⁻¹ * g) = mat g⁻¹ * mat g := rfl
  rw [← this, inv_mul_cancel]; rfl
private theorem gInf_le_pk {W : Spc F E d} {k : UA σ W.J} (hk : k ∈ gInf σ W) : k ∈ UAt σ W (evI F) := by
  induction hk using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one =>
    intro u _
    have : mat (1 : UA σ W.J) = 1 := rfl
    rw [this, sub_self, smul_zero]
  | mul g h _ _ hg hh =>
    intro u hu
    have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
      have : mat (g * h) = mat g * mat h := rfl
      rw [this, sub_mul, one_mul]; abel
    rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]
  | inv g _ hg =>
    intro u hu
    have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by rw [mul_sub, mat_inv_mul_pk, mul_one, neg_sub]
    rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]
private noncomputable def pureL_pk {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : SInf F κ →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun f := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ
  map_add' f g := funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
  map_smul' c f := funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
end UpperTheory.PolynomialDataFiniteKType₂
open UpperTheory.PolynomialDataFiniteKType₂ in
theorem UpperTheory.exists_finiteDimensional_weil_archimedean_orbit :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → ∀ Φ ∈ PolData B M, ∃ V : Submodule ℂ (Fn F n d), FiniteDimensional ℂ V ∧ V ≤ schA F (Fin n × Fin d) ∧ ∀ k ∈ gInf σ W, om (1, k) Φ ∈ V := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om hP Φ hΦ
  have hK : ∀ k ∈ gInf σ W, k ∈ KInf σ W B.emb := fun k hk =>
    ⟨gInf_le_pk hk, fun w => by
      rw [GlobalTheory.ThK.Dbl.Prs.cartan_one (hP.skew.sig w) (hP.skew.cartan w)]
      exact Commute.one_right _⟩
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, φ, h1, h2, rfl⟩ := hx
    have hfin : {v | ¬ φ v = M.vac v}.Finite := h2
    have hD : GlobalTheory.ThK.Dbl.Prs.Dat B M hfin.toFinset f φ :=
      ⟨hf, h1, fun v hv => by simpa using hv⟩
    obtain ⟨g, hg, e⟩ := hD.pureA hP.good
    obtain ⟨U, hU, hU'⟩ := _root_.GlobalTheory.ThK.Dbl.polFin_k hP f hf
    refine ⟨U.map (pureL_pk φ), inferInstance, ?_, fun k hk => ?_⟩
    · rintro _ ⟨f', -, rfl⟩
      exact Submodule.subset_span ⟨f', g, hg, e f'⟩
    · obtain ⟨A, hA⟩ := _root_.GlobalTheory.ThK.Dbl.Prs.inf_op_k _root_.PositivityTheory.ThKF.A.archOp_k hP (hK k hk)
      have hact := (hA f hf).2
      exact ⟨A f, hU' k (hK k hk) _ hact, (hact _ (hD.rest hP.good)).symm⟩
  | zero => exact ⟨⊥, inferInstance, bot_le, fun k _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨V, h1, h2, h3⟩ := hx
    obtain ⟨V', h1', h2', h3'⟩ := hy
    exact ⟨V ⊔ V', inferInstance, sup_le h2 h2', fun k hk => by
      rw [map_add (f := _)]; exact Submodule.add_mem_sup (h3 k hk) (h3' k hk)⟩
  | smul c x _ hx =>
    obtain ⟨V, h1, h2, h3⟩ := hx
    exact ⟨V, h1, h2, fun k hk => by rw [map_smul]; exact V.smul_mem c (h3 k hk)⟩
end
end
end
