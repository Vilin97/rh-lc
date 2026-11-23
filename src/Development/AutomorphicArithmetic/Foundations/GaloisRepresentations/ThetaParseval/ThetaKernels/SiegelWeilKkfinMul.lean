module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinBase
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinGsT
public import Development.WeilBound.ThetaLifts.LatticeBasics.BoxFinV
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.CompactStandardSubgroup.KCptPf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled
import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactOfUnits
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseFinLevel
public import Development.WeilBound.ThetaLifts.LatticeBasics.BoxFinC
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.ExistsAdelePiInf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.FirstFrameHalfEqMul
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinCpt

section

@[expose] public section



section
noncomputable section
attribute [local instance] GlobalTheory.ThK.Dbl.St.ae_ring GlobalTheory.ThK.Dbl.St.ae_t2 GlobalTheory.ThK.Dbl.St.ae_smul
open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem isCompact_K_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsCompact (d.K : Set d.G) := by
  have hB := d.ok.good
  have hK := d.ok.stdK
  obtain ⟨Φ, hΦ, eΦ⟩ := GlobalTheory.ThK.Dbl.St.exists_section hB.cm d.B.emb
  have hI : IsCompact (intHat F E : Set (AE F E)) := SiegelEisensteinSeries.BRoad.isCompact_intHat
  have hfe : finOne F = GlobalTheory.ThK.Dbl.St.eF F := rfl
  set T : Set (AE F E) := Φ '' Set.univ.pi (fun _ => Metric.closedBall (0 : ℂ) 1) + (intHat F E : Set (AE F E))
    with hTdef
  have hT : IsCompact T := ((isCompact_univ_pi fun _ => isCompact_closedBall _ _).image hΦ).add hI
  have hentry : ∀ k ∈ d.K, ∀ i j, inFrame d.b k i j ∈ T := by
    intro k hk i j
    obtain ⟨h1, h2⟩ := (hK k).1 hk
    rw [eΦ (inFrame d.b k i j)]
    refine Set.add_mem_add ⟨_, fun w _ => ?_, rfl⟩ ?_
    · rw [mem_closedBall_zero_iff]
      have hu : (inFrame d.b k).map (piInf (d.B.emb w)) ∈ Matrix.unitaryGroup (Fin d.n ⊕ Fin d.n) ℂ :=
        Matrix.mem_unitaryGroup_iff.2 (by rw [Matrix.star_eq_conjTranspose]; exact h1 w)
      exact entry_norm_bound_of_unitary hu i j
    · rw [← hfe]
      exact h2 k (Set.mem_insert _ _) i j
  set S : Set (Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) :=
    (fun M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) => incM F d.b.1 * M * incM F (d.b⁻¹).1) ''
      Set.univ.pi (fun _ => Set.univ.pi fun _ => T) with hSdef
  have hS : IsCompact S :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hT).image
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
  have hmat : ∀ k ∈ d.K, mat2 k ∈ S := fun k hk => ⟨inFrame d.b k, fun i _ j _ => hentry k hk i j, by
    show incM F d.b.1 * (incM F (d.b⁻¹).1 * mat2 k * incM F d.b.1) * incM F (d.b⁻¹).1 = mat2 k
    simp only [Matrix.mul_assoc, GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv, Matrix.one_mul]⟩
  have hp : ∀ w, Continuous (piInf (d.B.emb w)) := fun w => GlobalTheory.Grow.continuous_infEmb_compInf F w (d.B.emb w)
  have hIc := hI.isClosed
  have hfr := GlobalTheory.EisBL.DoubledParabolic.continuous_inFrame (σ := σ) (Y := d.Y) d.b
  have hKset : (d.K : Set d.G) =
      (⋂ w, {k | (inFrame d.b k).map (piInf (d.B.emb w)) * ((inFrame d.b k).map (piInf (d.B.emb w)))ᴴ = 1}) ∩
        ((⋂ i, ⋂ j, {k : d.G | finOne F • inFrame d.b k i j ∈ intHat F E}) ∩
          (⋂ i, ⋂ j, {k : d.G | finOne F • inFrame d.b k⁻¹ i j ∈ intHat F E})) := by
    ext k
    simp only [SetLike.mem_coe, hK k, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, Set.forall_mem_insert,
      Set.mem_singleton_iff, forall_eq]
  have hKc : IsClosed (d.K : Set d.G) := by
    rw [hKset]
    refine (isClosed_iInter fun w => isClosed_eq ?_ continuous_const).inter
      ((isClosed_iInter fun i => isClosed_iInter fun j => hIc.preimage ?_).inter
        (isClosed_iInter fun i => isClosed_iInter fun j => hIc.preimage ?_))
    · exact (hfr.matrix_map (hp w)).matrix_mul (hfr.matrix_map (hp w)).matrix_conjTranspose
    · exact (hfr.matrix_elem i j).const_smul (finOne F)
    · exact ((hfr.comp continuous_inv).matrix_elem i j).const_smul (finOne F)
  exact GlobalTheory.ThK.Dbl.St.isCompact_of_units (UG (cA σ) (dbl (incM F d.Y.J))) (GlobalTheory.EisBL.DoubledGroupTopology.isClosed_doubled_group σ d.Y) d.K hKc S hS
    fun k hk => ⟨hmat k hk, hmat k⁻¹ (d.K.inv_mem hk)⟩
end PositivityTheory.SiegelWeilFormula.KK
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinVac

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem splitting_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsSplitting (adeleClass F) d.B.ψ d.dd (actB (cA σ)) d.om :=
  d.ok.dbl.weil.2.1.toIsSplitting
theorem imp_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (k : d.G) :
    Box.Imp d.B.ψ (d.om k) fun w => d.dd.e (actB (cA σ) k (d.dd.e.symm w)) :=
  ⟨(_root_.PositivityTheory.SiegelWeilFormula.KK.splitting_k d).pres k, (_root_.PositivityTheory.SiegelWeilFormula.KK.splitting_k d).adm k, fun w w' => by simp only [actB, map_add (f := _), Matrix.add_mul],
    fun c w => by simp only [actB, map_smul, Matrix.smul_mul], fun w φ hφ => by
      have := (_root_.PositivityTheory.SiegelWeilFormula.KK.splitting_k d).impl k (d.dd.e.symm w) φ hφ
      rwa [Darboux.rho, LinearEquiv.apply_symm_apply] at this⟩
theorem om_D_k (k : d.G) {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) {Φ : d.Fn}
    (hΦ : Φ ∈ d.sch) : d.om k (Box.D (d.dd.e u) Φ) = Box.D (d.dd.e (actB (cA σ) k u)) (d.om k Φ) := by
  have := (_root_.PositivityTheory.SiegelWeilFormula.KK.imp_k d k).inter d.ok.good.std (Box.at_e d.dd.e hu) hΦ
  rwa [LinearEquiv.symm_apply_apply] at this
theorem D_kfS_k {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) {Φ : d.Fn} (h : Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d) :
    Box.D (d.dd.e u) Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d := by
  obtain ⟨N, _, h0, h1, h2⟩ := h
  obtain ⟨N', _, h4⟩ := Box.exists_D_fin N h0
  refine ⟨Submodule.span ℂ {z | ∃ v, At (evI F) v ∧ ∃ x ∈ N, z = Box.D (d.dd.e v) x},
    Submodule.finiteDimensional_of_le (S₂ := N') (Submodule.span_le.2 ?_), Submodule.span_le.2 ?_,
    Submodule.subset_span ⟨u, hu, Φ, h1, rfl⟩, fun k hk z hz => ?_⟩
  · rintro _ ⟨v, -, x, hx, rfl⟩
    exact h4 _ _ x hx
  · rintro _ ⟨v, -, x, hx, rfl⟩
    exact Box.DP_mem (h0 hx) _ _
  · induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, hv, x, hx, rfl⟩ := hz
      exact Submodule.subset_span ⟨_, Box.at_actB k hv, _, h2 k hk x hx, _root_.PositivityTheory.SiegelWeilFormula.KK.om_D_k k hv (h0 hx)⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add _ _ _ _ i j => rw [map_add]; exact add_mem i j
    | smul c _ _ i => rw [map_smul]; exact Submodule.smul_mem _ _ i
theorem vac_kfS_k (θ : InfinitePlace F → Matrix (Fin d.m) (Fin d.m) ℂ)
    (θ' : InfinitePlace F → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) ℂ)
    (hc : ∀ k ∈ d.K, ∀ w, Commute ((mat2 k).map (piInf (d.B.emb w))) (θ' w)) (ε : InfinitePlace F → ℤˣ) {Φ : d.Fn}
    (hΦ : Φ ∈ d.sch) (hv : ∀ u u', At (evI F) u → At (evI F) u' → Box.Rel d.B.emb ε θ θ' u u' →
      Box.D (d.dd.e u') Φ = Complex.I • Box.D (d.dd.e u) Φ) : Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d := by
  have hB := d.ok.good
  have hs := _root_.PositivityTheory.SiegelWeilFormula.KK.splitting_k d
  obtain ⟨Λ, l1, l2, s, s1, s2⟩ := _root_.GlobalTheory.ThK.Dbl.finLevel_k F E σ d.B d.m d.n d.A d.Y hB d.κ d.dd d.K (_root_.PositivityTheory.SiegelWeilFormula.KK.isCompact_K_k d) Φ hΦ
  have radd : ∀ u (x y : d.Fn), d.dd.rho d.B.ψ u (x + y) = d.dd.rho d.B.ψ u x + d.dd.rho d.B.ψ u y := fun u x y =>
    funext fun _ => mul_add _ _ _
  have rsmul : ∀ u (c : ℂ) (x : d.Fn), d.dd.rho d.B.ψ u (c • x) = c • d.dd.rho d.B.ψ u x := fun u c x =>
    funext fun _ => mul_left_comm _ _ _
  let N : Submodule ℂ d.Fn :=
    { carrier := {Ψ | Ψ ∈ d.sch ∧ (∀ u ∈ Λ, d.dd.rho d.B.ψ u Ψ = Ψ) ∧ ∀ u u', At (evI F) u → At (evI F) u' →
        Box.Rel d.B.emb ε θ θ' u u' → Box.D (d.dd.e u') Ψ = Complex.I • Box.D (d.dd.e u) Ψ}
      zero_mem' := ⟨zero_mem _, fun u _ => funext fun _ => mul_zero _, fun _ _ _ _ _ => by
        simp only [Box.D, Box.DP_zero, smul_zero]⟩
      add_mem' := fun h h' => ⟨add_mem h.1 h'.1, fun u hu => by rw [radd, h.2.1 u hu, h'.2.1 u hu], fun u u' a b c => by
        have e1 := h.2.2 u u' a b c
        have e2 := h'.2.2 u u' a b c
        simp only [Box.D] at e1 e2 ⊢
        rw [Box.DP_add h.1 h'.1, Box.DP_add h.1 h'.1, e1, e2, smul_add]⟩
      smul_mem' := fun t _ h => ⟨Submodule.smul_mem _ _ h.1, fun u hu => by rw [rsmul, h.2.1 u hu], fun u u' a b c => by
        have e1 := h.2.2 u u' a b c
        simp only [Box.D] at e1 ⊢
        rw [Box.DP_smul h.1, Box.DP_smul h.1, e1, smul_comm]⟩ }
  refine ⟨N, ?_, fun _ h => h.1, ⟨hΦ, l2, hv⟩, fun k hk Ψ h => ⟨hs.pres k _ h.1, fun u hu => ?_, fun u u' a b c => ?_⟩⟩
  · refine FiniteDimensional.of_injective ((LinearMap.pi fun y : s => LinearMap.proj y.1) ∘ₗ N.subtype)
      ((injective_iff_map_eq_zero _).2 fun Ψ h0 => Subtype.ext (funext fun z => ?_))
    have sp : ∀ x (y : d.κ → AF F), (∀ i, evI F (y i) = 0) → Dense.pt x 0 + y = Dense.pt x (Box.fn y) := fun x y hy => by
      rw [← Box.pt_self (Dense.pt x 0 + y), Box.nf_add, Box.nf_pt, show Box.nf y = 0 from funext hy, add_zero]
      exact congrArg (Dense.pt x) (funext fun i => zero_add _)
    have z0 : ∀ i, evI F (Dense.pt 0 (Box.fn z) i) = 0 := fun i => congrFun (Dense.evI_pt 0 (Box.fn z)) i
    have := s2 Ψ.1 Ψ.2.2.1 (Dense.pt (Box.nf z) 0) (Box.at_pt _) (fun y hy => ?_) _ z0
    · rwa [sp _ _ z0, show Box.fn (Dense.pt 0 (Box.fn z)) = Box.fn z from rfl, Box.pt_self] at this
    obtain ⟨f, e⟩ := Box.slice Ψ.2.1 (Box.fn y)
    have g : Box.Gs d.dd.e d.B.emb ε θ θ' f := fun u u' a b c => SchwartzMap.ext fun x => by
      have := congrFun (Ψ.2.2.2 u u' a b c) (Dense.pt x (Box.fn y))
      rwa [Pi.smul_apply, Box.D, Box.D, Box.DP_pt e, Box.DP_pt e] at this
    rw [sp _ _ (s1 y hy), e]
    by_cases hf : f = 0
    · rw [hf]; rfl
    obtain ⟨_, hg⟩ := g.gau hB.cm hf
    refine (hg.ne 0 ?_).elim
    rw [← e, ← show Box.nf y = 0 from funext (s1 y hy), Box.pt_self]
    exact congrFun h0 ⟨y, hy⟩
  · rw [← Box.actB_inv k u, ← hs.impl k _ _ h.1, h.2.1 _ ((l1 u hu).2.2 _ (inv_mem hk))]
  · rw [← Box.actB_inv k u, ← Box.actB_inv k u', ← _root_.PositivityTheory.SiegelWeilFormula.KK.om_D_k k (Box.at_actB _ a) h.1, ← _root_.PositivityTheory.SiegelWeilFormula.KK.om_D_k k (Box.at_actB _ b) h.1,
      ← map_smul]
    refine congrArg (d.om k) (h.2.2 _ _ (Box.at_actB _ a) (Box.at_actB _ b) fun w => ?_)
    have cm := (hc k⁻¹ (inv_mem hk) w).eq
    simp only [actB, Matrix.map_mul, Matrix.transpose_map, c w, Matrix.smul_mul, Matrix.mul_assoc, ← Matrix.transpose_mul]
    exact congrArg (fun x => _ • (_ * (_ * xᵀ))) cm
end PositivityTheory.SiegelWeilFormula.KK
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinVarB

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open Matrix
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem exists_at_place_k (w : InfinitePlace F) (V : Matrix (Fin d.m) (Fin d.n) ℂ) :
    ∃ V' : Mx F E d.m d.n, At (evI F) V' ∧ ∀ w', d.cw w' V' = if w' = w then V else 0 := by
  have h := d.ok.good.cm
  choose x hx hz using fun i j => GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h d.B.emb fun w' =>
    if w' = w then V i j else 0
  refine ⟨Matrix.of x, fun c hc => Matrix.ext fun i j => hx i j c hc, fun w' => ?_⟩
  ext i j
  show piInf (d.B.emb w') (x i j) = _
  rw [hz i j w']
  split_ifs <;> rfl
theorem mZ_place_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (tA : Matrix (Fin d.n) (Fin d.n) (AE F E)) (htA : _root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d = _root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d * tA)
    {V' : Mx F E d.m d.n} {V : Matrix (Fin d.m) (Fin d.n) ℂ} (hV : ∀ w', d.cw w' V' = if w' = w then V else 0)
    (X : Mx F E d.m d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d (V' * tAᵀ) X = -(2 * ((((R.ε : ℤ) : ℂ)) * trace ((d.cw w X)ᵀ * d.A.J.map (d.B.emb w).1 * V.map star)).re) := by
  have e1 : V' * tAᵀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ = V' * (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d)ᵀ := by rw [htA, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k, e1, _root_.PositivityTheory.SiegelWeilFormula.KK.trace_sp_k, Finset.sum_eq_single w]
  · congr 3
    have hX : (X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ).map (piInf (d.B.emb w)) = d.cw w X * ((d.b.1.map (d.B.emb w).1).toCols₂)ᵀ := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KK.map_mul_incM_T_k]; rfl
    have hVb : (V' * (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d)ᵀ).map (piInf (d.B.emb w)) = V * ((d.b.1.map (d.B.emb w).1).toCols₁)ᵀ := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KK.map_mul_incM_T_k]
      have := hV w
      rw [if_pos rfl] at this
      rw [show V'.map (piInf (d.B.emb w)) = d.cw w V' from rfl, this]
      rfl
    rw [hX, hVb]
    exact trace_form_sign_eq (_root_.PositivityTheory.SiegelWeilFormula.KK.frame_form_k R w) (d.cw w X) V
  · intro w' _ hw'
    have hVb : (V' * (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d)ᵀ).map (piInf (d.B.emb w')) = 0 := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KK.map_mul_incM_T_k]
      have := hV w'
      rw [if_neg hw'] at this
      rw [show V'.map (piInf (d.B.emb w')) = d.cw w' V' from rfl, this, Matrix.zero_mul]
    rw [hVb]
    simp
  · intro h; exact absurd (Finset.mem_univ w) h
theorem var_span'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (k : Fin d.m × Fin d.n × Bool) :
    ∃ (Z₁ Z₂ : Mx F E d.m d.n) (c₁ c₂ : ℂ), At (evI F) Z₁ ∧ At (evI F) Z₂ ∧
      ∀ X, evX (MvPolynomial.X k) (R.loc w X) = c₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d Z₁ X : ℂ) + c₂ * (_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d Z₂ X : ℂ) := by
  obtain ⟨tA, htA⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.firstColumns_eq_diag_mul (d := d)
  set τ := d.B.emb w
  set fr := (R.fr w).1
  set fi := ((R.fr w)⁻¹).1
  set A := d.A.J.map τ.1
  set e : ℂ := ((R.ε : ℤ) : ℂ)
  have he : e * e = 1 := by rcases Int.units_eq_one_or R.ε with h | h <;> simp [e, h]
  have hes : star e = e := by simp [e]
  have hz : star R.ζ * R.ζ = 1 := by rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp [Complex.ext_iff]
  have hfi : fr * fi = 1 := by simp only [fr, fi]; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hif : fi * fr = 1 := by simp only [fr, fi]; rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  set P := (((R.sg w : ℤ) : ℂ) * R.ζ) • (fr.map star * frᵀ)
  have hAP : A * P = 1 := by
    have hA := A_eq hfi hz (R.hfr w)
    rw [show d.A.J.map (d.B.emb w).1 = A from rfl] at hA
    rw [hA]
    simp only [P, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have t1 : fiᵀ * fi.map star * (fr.map star * frᵀ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (fi.map star), ← mapStar_mul, hif]
      rw [show (1 : Matrix (Fin d.m) (Fin d.m) ℂ).map star = 1 from Matrix.map_one star (star_zero _) (star_one _)]
      rw [Matrix.one_mul, ← transpose_mul, hfi, transpose_one]
    rw [t1]
    have hs2 : ((R.sg w : ℤ) : ℂ) * R.ζ * (((R.sg w : ℤ) : ℂ) * star R.ζ) = 1 := by
      calc _ = (((R.sg w : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ)) * (star R.ζ * R.ζ) := by ring
        _ = 1 := by rw [hz, mul_one]; rcases Int.units_eq_one_or (R.sg w) with h | h <;> simp [h]
    rw [hs2, one_smul]
  have key : ∀ M : Matrix (Fin d.m) (Fin d.n) ℂ, ∃ Z : Mx F E d.m d.n, At (evI F) Z ∧
      ∀ X, (_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d Z X : ℂ) = -(2 * e) * ((trace ((d.cw w X)ᵀ * M)).re : ℂ) := by
    intro M
    obtain ⟨V', hV'a, hV'⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.exists_at_place_k (d := d) w ((P * M).map star)
    refine ⟨V' * tAᵀ, at_mul hV'a _, fun X => ?_⟩
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_place_k R w tA htA hV' X]
    have : (d.cw w X)ᵀ * A * ((P * M).map star).map star = (d.cw w X)ᵀ * M := by
      rw [show ((P * M).map star).map star = P * M by ext i j; simp only [Matrix.map_apply, star_star], ← Matrix.mul_assoc, Matrix.mul_assoc _ A, hAP,
        Matrix.mul_one]
    rw [show d.A.J.map (d.B.emb w).1 = A from rfl, this]
    have hre : (e * trace ((d.cw w X)ᵀ * M)).re = e.re * (trace ((d.cw w X)ᵀ * M)).re := by
      rcases Int.units_eq_one_or R.ε with h | h <;> simp [e, h]
    rw [hre]
    rcases Int.units_eq_one_or R.ε with h | h <;> simp [e, h] <;> ring
  have hM : ∀ (c : ℂ) (x : Matrix (Fin d.m) (Fin d.n) ℂ),
      trace (xᵀ * Matrix.of fun b j => if j = k.2.1 then c * fi k.1 b else 0) = c * (fi * x) k.1 k.2.1 := fun c x => by
    simp only [trace, diag_apply, Matrix.mul_apply, transpose_apply, of_apply, mul_ite, mul_zero]
    rw [Finset.sum_eq_single k.2.1 (fun j _ hj => by simp [hj]) (by simp)]
    simp only [if_pos rfl, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by simp only [if_true]; ring
  obtain ⟨Z₁, h1, e1⟩ := key (Matrix.of fun b j => if j = k.2.1 then 1 * fi k.1 b else 0)
  obtain ⟨Z₂, h2, e2⟩ := key (Matrix.of fun b j => if j = k.2.1 then (-Complex.I) * fi k.1 b else 0)
  have hl : ∀ X, evX (MvPolynomial.X k) (R.loc w X) =
      if k.2.2 then (fi * d.cw w X) k.1 k.2.1 else star ((fi * d.cw w X) k.1 k.2.1) := fun X => by
    simp only [evX, MvPolynomial.eval_X, _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc, Matrix.map_apply]
    split_ifs <;> (try simp only [star_star]) <;> rfl
  have hsplit : ∀ z : ℂ, z = (z.re : ℂ) + Complex.I * ((-Complex.I * z).re : ℂ) := fun z => by
    apply Complex.ext <;> simp
  have hsplit' : ∀ z : ℂ, star z = (z.re : ℂ) - Complex.I * ((-Complex.I * z).re : ℂ) := fun z => by
    apply Complex.ext <;> simp
  refine ⟨Z₁, Z₂, -(e / 2) * (if k.2.2 then 1 else 1), -(e / 2) * (if k.2.2 then Complex.I else -Complex.I), h1, h2,
    fun X => ?_⟩
  rw [hl X, e1 X, e2 X, hM, hM, one_mul]
  have hinv : -(e / 2) * (-(2 * e)) = 1 := by linear_combination he
  split_ifs
  · conv_lhs => rw [hsplit ((fi * d.cw w X) k.1 k.2.1)]
    linear_combination (-(((fi * d.cw w X) k.1 k.2.1).re : ℂ) - Complex.I * ((-Complex.I * (fi * d.cw w X) k.1 k.2.1).re : ℂ)) * hinv
  · rw [hsplit' ((fi * d.cw w X) k.1 k.2.1)]
    linear_combination (-(((fi * d.cw w X) k.1 k.2.1).re : ℂ) + Complex.I * ((-Complex.I * (fi * d.cw w X) k.1 k.2.1).re : ℂ)) * hinv
end PositivityTheory.SiegelWeilFormula.KK
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinMul

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
def Tl_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.Fn →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := d.T
  map_add' Φ Ψ := funext fun X => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.add_apply, ← map_add (f := _)]
    congr 1
    funext z
    exact mul_add _ _ _
  map_smul' c Φ := funext fun X => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.smul_apply, RingHom.id_apply, ← map_smul]
    congr 1
    funext z
    exact mul_left_comm _ _ _
def TK_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Submodule ℂ (Mx F E d.m d.n → ℂ) := (_root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d).map (_root_.PositivityTheory.SiegelWeilFormula.KK.Tl_k d)
theorem D_dg_mem_k {Φ : d.Fn} (hΦ : Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d) {Z : Mx F E d.m d.n} (hZ : At (evI F) Z) :
    Box.D (d.dd.e (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d :=
  _root_.PositivityTheory.SiegelWeilFormula.KK.D_kfS_k (fun c hc => by rw [← Matrix.smul_mul, hZ c hc, Matrix.zero_mul]) hΦ
theorem mul_var_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (k : Fin d.m × Fin d.n × Bool) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d) : (fun X => evX (MvPolynomial.X k) (R.loc w X) * f X) ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  obtain ⟨Φ, hΦ, rfl⟩ := hf
  obtain ⟨Z₁, Z₂, c₁, c₂, h1, h2, e⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.var_span'_k R w k
  have hc : (-(2 * Real.pi * Complex.I) : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨(c₁ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ +
    (c₂ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₂ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ,
    add_mem (Submodule.smul_mem _ _ (_root_.PositivityTheory.SiegelWeilFormula.KK.D_dg_mem_k hΦ h1)) (Submodule.smul_mem _ _ (_root_.PositivityTheory.SiegelWeilFormula.KK.D_dg_mem_k hΦ h2)), funext fun X => ?_⟩
  have t := congrFun ((_root_.PositivityTheory.SiegelWeilFormula.KK.Tl_k d).map_add ((c₁ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ)
    ((c₂ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₂ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ)) X
  simp only [map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at t
  change d.T _ X = _ at t
  change d.T _ X = _ * d.T Φ X
  rw [t]
  change _ * d.T _ X + _ * d.T _ X = _
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.T_D_dg_k (_root_.PositivityTheory.SiegelWeilFormula.KK.mem_sch_k hΦ) h1, _root_.PositivityTheory.SiegelWeilFormula.KK.T_D_dg_k (_root_.PositivityTheory.SiegelWeilFormula.KK.mem_sch_k hΦ) h2, e X]
  field_simp
theorem mul_pol_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (Q : PX d.m d.n) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d) :
    (fun X => evX Q (R.loc w X) * f X) ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  induction Q using MvPolynomial.induction_on generalizing f with
  | C a =>
    have : (fun X => evX (MvPolynomial.C a) (R.loc w X) * f X) = a • f := funext fun X => by
      simp [evX]
    rw [this]; exact Submodule.smul_mem _ _ hf
  | add p q hp hq =>
    have : (fun X => evX (p + q) (R.loc w X) * f X) = (fun X => evX p (R.loc w X) * f X) + fun X => evX q (R.loc w X) * f X :=
      funext fun X => by simp [evX, add_mul]
    rw [this]; exact add_mem (hp hf) (hq hf)
  | mul_X p k hp =>
    have : (fun X => evX (p * MvPolynomial.X k) (R.loc w X) * f X) =
        fun X => evX (MvPolynomial.X k) (R.loc w X) * (evX p (R.loc w X) * f X) := funext fun X => by
      simp only [evX, map_mul]; ring
    rw [this]; exact _root_.PositivityTheory.SiegelWeilFormula.KK.mul_var_k R w k (hp hf)
theorem mul_prod_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (P : InfinitePlace F → PX d.m d.n) (s : Finset (InfinitePlace F)) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d) : (fun X => (∏ w ∈ s, evX (P w) (R.loc w X)) * f X) ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  induction s using Finset.induction_on with
  | empty => simpa using hf
  | insert w s hw ih =>
    have : (fun X => (∏ w ∈ insert w s, evX (P w) (R.loc w X)) * f X) =
        fun X => evX (P w) (R.loc w X) * ((∏ w ∈ s, evX (P w) (R.loc w X)) * f X) := funext fun X => by
      rw [Finset.prod_insert hw, mul_assoc]
    rw [this]; exact _root_.PositivityTheory.SiegelWeilFormula.KK.mul_pol_k R w (P w) ih
theorem vac_mem_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ}
    (hg : g ∈ SB _) : _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  have hgen : _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g ∈ R.fock := Submodule.subset_span ⟨fun _ => 1, g, hg, funext fun X => by
    simp [_root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k, fP, evX]⟩
  obtain ⟨Φ, hΦ, e⟩ := (hT.1 F E σ d).2.1 _ ((hF F E σ d R).1 hgen)
  refine ⟨Φ, _root_.PositivityTheory.SiegelWeilFormula.KK.vac_kfS_k (_root_.PositivityTheory.SiegelWeilFormula.KK.thA_k R) (_root_.PositivityTheory.SiegelWeilFormula.KK.thB_k d R.ε) (fun k hk w => _root_.PositivityTheory.SiegelWeilFormula.KK.commute_thB_k R hk w) (fun _ => 1) hΦ fun u u' hu hu' hr => ?_, e⟩
  have m1 : Box.D (d.dd.e u') Φ ∈ d.sch := Box.DP_mem hΦ _ _
  have m2 : Box.D (d.dd.e u) Φ ∈ d.sch := Box.DP_mem hΦ _ _
  refine sub_eq_zero.1 ((hT.1 F E σ d).2.2 _ (sub_mem m1 (Submodule.smul_mem _ _ m2)) (funext fun X => ?_))
  have t := congrFun ((_root_.PositivityTheory.SiegelWeilFormula.KK.Tl_k d).map_sub (Box.D (d.dd.e u') Φ) (Complex.I • Box.D (d.dd.e u) Φ)) X
  simp only [map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at t
  change d.T _ X = d.T _ X - Complex.I * d.T _ X at t
  rw [t, _root_.PositivityTheory.SiegelWeilFormula.KK.vac_rel_k R g hΦ e hu hu' hr X, sub_self]
  rfl
theorem fock_le_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.fock ≤ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨P, g, hg, rfl⟩
  have e : (fun X => (∏ w ∈ Finset.univ, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2) =
      fun X => (∏ w ∈ Finset.univ, evX (P w) (R.loc w X)) * _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g X := funext fun X => by
    simp only [fP, _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k, Finset.prod_mul_distrib]; ring
  rw [SetLike.mem_coe, e]
  exact _root_.PositivityTheory.SiegelWeilFormula.KK.mul_prod_k R P _ (_root_.PositivityTheory.SiegelWeilFormula.KK.vac_mem_k hT hF R hg)
theorem polyKFin_of_k : _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k := by
  intro hT hF F E _ _ _ _ _ σ d R Φ hΦ hf
  obtain ⟨Φ', h', e⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.fock_le_k hT hF R hf
  have : Φ = Φ' := (sub_eq_zero.1 ((hT.1 F E σ d).2.2 _ (sub_mem hΦ (_root_.PositivityTheory.SiegelWeilFormula.KK.mem_sch_k h')) (by
    rw [show d.T (Φ - Φ') = _root_.PositivityTheory.SiegelWeilFormula.KK.Tl_k d (Φ - Φ') from rfl, map_sub]
    exact sub_eq_zero.2 e.symm))).symm ▸ rfl
  rw [this]
  exact _root_.PositivityTheory.SiegelWeilFormula.KK.kFin_of_mem_k h'
end PositivityTheory.SiegelWeilFormula.KK
end
end
end
end
