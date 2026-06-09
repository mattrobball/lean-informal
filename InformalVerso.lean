module

-- Verso rendering layer. Re-exports the verso-free core plus the Verso block
-- expanders. Downstream projects that do NOT need Verso should `require` the
-- `informal-core` package (in the `core/` subdirectory) instead and
-- `import Informal` directly — that pulls zero verso / subverso / md4lean.
public import Informal
public import InformalVerso.VersoBlock
public import InformalVerso.Extract
public import InformalVerso.EmitStandalone
