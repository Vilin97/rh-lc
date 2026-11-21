module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexConjUniformizerPowerDiagonalGLReindex
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_conj_uniformizerPowerDiagonalGL_reindex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (σ : n ≃ n') (e : n → ℤ),
    ((KO k n').map (MulAut.conj (torusElt ϖ (e ∘ σ.symm))).toMonoidHom).relIndex (KO k n') =
      ((KO k n).map (MulAut.conj (torusElt ϖ e)).toMonoidHom).relIndex (KO k n) := by
  intro k _ _ _ _ ϖ n n' _ _ _ _ σ e
  let φ := GlobalTheory.ReindexTorus.reindexGL k σ
  have htorus : φ (torusElt ϖ e) = torusElt ϖ (e ∘ σ.symm) := by
    apply Units.ext
    change (GlobalTheory.ReindexTorus.reindexGL k σ (torusElt ϖ e)).val = _
    rw [GlobalTheory.ReindexTorus.val_reindexGL]
    simp only [torusElt, val_diagT, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv,
      Function.comp_def]
  have hKO : (KO k n).map φ.toMonoidHom = KO k n' :=
    GlobalTheory.ReindexTorus.map_reindexGL_KO k σ
  have hconj (g : GL n k) (H : Subgroup (GL n k)) :
      (H.map (MulAut.conj g).toMonoidHom).map φ.toMonoidHom =
        (H.map φ.toMonoidHom).map (MulAut.conj (φ g)).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x : 1
    simp [map_mul, map_inv]
  rw [← htorus, ← hKO, ← hconj]
  exact Subgroup.relIndex_map_map_of_injective _ _ φ.injective
