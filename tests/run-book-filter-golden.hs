module Main where

import Control.Exception (IOException, bracket, catch, evaluate)
import Control.Monad (forM_, unless, when)
import Data.List (intercalate)
import Data.Maybe (fromMaybe, isNothing)
import DependencyGraphTests (runDependencyPlanTests)
import SemanticExprTests (semanticExprFailures)
import System.Directory (
  Permissions (executable),
  createDirectory,
  createDirectoryIfMissing,
  doesFileExist,
  findExecutable,
  getCurrentDirectory,
  getPermissions,
  getTemporaryDirectory,
  removeDirectoryRecursive,
  removeFile,
  setPermissions,
 )
import System.Environment (getEnvironment, lookupEnv)
import System.Exit (ExitCode (..), exitFailure)
import System.FilePath (takeFileName, (</>))
import System.IO (hClose, hPutStrLn, openTempFile, stderr)
import System.Process (
  CreateProcess (cwd, env),
  proc,
  readCreateProcessWithExitCode,
  readProcessWithExitCode,
 )

data Golden = Golden
  { goldenName :: String
  , goldenInput :: FilePath
  , goldenExpected :: FilePath
  }

data FailureCase = FailureCase
  { failureName :: String
  , failureInput :: FilePath
  , failureExpectedStderr :: String
  }

main :: IO ()
main = runSuite `catch` infrastructureFailure
 where
  infrastructureFailure :: IOException -> IO ()
  infrastructureFailure error = do
    hPutStrLn stderr ("book-filter golden test infrastructure failed: " <> show error)
    exitFailure

runSuite :: IO ()
runSuite = do
  root <- getCurrentDirectory
  let filterBin = root </> "build" </> "book-filter"
  filterExists <- doesFileExist filterBin
  unless filterExists $ do
    hPutStrLn stderr ("missing filter binary: " <> filterBin)
    hPutStrLn stderr "run `make build/book-filter` or `make test`"
    exitFailure

  pandoc <- fromMaybe "pandoc" <$> lookupEnv "PANDOC_BIN"
  forM_ [pandoc, "diff"] $ \command -> do
    found <- findExecutable command
    when (isNothing found) $ do
      hPutStrLn stderr ("book-filter golden tests require executable: " <> command)
      exitFailure
  tmpBase <- getTemporaryDirectory
  bracket (createTestDirectory tmpBase) removeDirectoryRecursive $ \tmp -> do
    goldenFailures <-
      mapM
        (runGolden root tmp filterBin)
        [ Golden
            "section references and notation links"
            ("tests" </> "fixtures" </> "section-notation.md")
            ("tests" </> "golden" </> "section-notation.tex")
        , Golden
            "semantic header math has readable PDF bookmarks without changing body math"
            ("tests" </> "fixtures" </> "header-math-bookmarks.md")
            ("tests" </> "golden" </> "header-math-bookmarks.tex")
        , Golden
            "notation links preserve relation, binary, and large-operator classes"
            ("tests" </> "fixtures" </> "notation-math-spacing.md")
            ("tests" </> "golden" </> "notation-math-spacing.tex")
        , Golden
            "table cells process block-form math metadata"
            ("tests" </> "fixtures" </> "table-mathmeta.md")
            ("tests" </> "golden" </> "table-mathmeta.tex")
        , Golden
            "theorem titles omit repeated English and Japanese environment labels"
            ("tests" </> "fixtures" </> "theorem-heading-labels.md")
            ("tests" </> "golden" </> "theorem-heading-labels.tex")
        , Golden
            "mathmeta inside a proof registers notation at its source position"
            ("tests" </> "fixtures" </> "mathmeta-in-proof.md")
            ("tests" </> "golden" </> "mathmeta-in-proof.tex")
        , Golden
            "mathmeta typed free-variable notation"
            ("tests" </> "fixtures" </> "mathmeta-freevars.md")
            ("tests" </> "golden" </> "mathmeta-freevars.tex")
        , Golden
            "mathmeta with scope preserves nested directives"
            ("tests" </> "fixtures" </> "mathmeta-with-nested.md")
            ("tests" </> "golden" </> "mathmeta-with-nested.tex")
        , Golden
            "mathmeta with scope applies inside nested block lists"
            ("tests" </> "fixtures" </> "mathmeta-with-nested-local-scope.md")
            ("tests" </> "golden" </> "mathmeta-with-nested-local-scope.tex")
        , Golden
            "half-open intervals after commands keep their brackets"
            ("tests" </> "fixtures" </> "math-bracket-intervals.md")
            ("tests" </> "golden" </> "math-bracket-intervals.tex")
        , Golden
            "repeated definitions share one anchor and external terms have no dangling links"
            ("tests" </> "fixtures" </> "term-anchor-scope.md")
            ("tests" </> "golden" </> "term-anchor-scope.tex")
        , Golden
            "a malformed index does not stop later Japanese localization"
            ("tests" </> "fixtures" </> "index-localization-malformed.md")
            ("tests" </> "golden" </> "index-localization-malformed.tex")
        , Golden
            "a malformed term marker does not block later well-formed markers"
            ("tests" </> "fixtures" </> "term-marker-malformed-recovery.md")
            ("tests" </> "golden" </> "term-marker-malformed-recovery.tex")
        , Golden
            "a term argument ending in an escaped backslash parses correctly"
            ("tests" </> "fixtures" </> "term-arg-trailing-backslash.md")
            ("tests" </> "golden" </> "term-arg-trailing-backslash.tex")
        , Golden
            "Japanese index uses canonical translated definitions and glossary labels"
            ("tests" </> "fixtures" </> "japanese-index.md")
            ("tests" </> "golden" </> "japanese-index.tex")
        , Golden
            "raw hierarchical \\index subentries pass through; flat entries become term entries"
            ("tests" </> "fixtures" </> "raw-index-entries.md")
            ("tests" </> "golden" </> "raw-index-entries.tex")
        ]

    expectedFailures <-
      mapM
        (runExpectedFailure root filterBin)
        [ FailureCase
            "distinct term keys cannot share a hyperlink slug"
            ("tests" </> "fixtures" </> "term-anchor-collision.md")
            "colliding term anchors"
        , FailureCase
            "case-distinct term keys cannot share a hyperlink slug"
            ("tests" </> "fixtures" </> "term-anchor-case-collision.md")
            "colliding term anchors"
        , FailureCase
            "notation use before definition is rejected"
            ("tests" </> "fixtures" </> "bad-notation-before-define.md")
            "[notation-filter] notation used before \\define or \\forward:"
        , FailureCase
            "later embedded metadata does not authorize earlier notation"
            ("tests" </> "fixtures" </> "bad-mathmeta-in-proof-order.md")
            "[notation-filter] notation used before \\define or \\forward:"
        , FailureCase
            "malformed embedded metadata is rejected"
            ("tests" </> "fixtures" </> "bad-mathmeta-in-proof.md")
            "malformed mathmeta block"
        , FailureCase
            "forwarded notation must later be defined"
            ("tests" </> "fixtures" </> "bad-forward-without-define.md")
            "[notation-filter] notation forwarded but never defined:"
        , FailureCase
            "forwarded terms must later be defined"
            ("tests" </> "fixtures" </> "bad-term-forward-without-define.md")
            "[term-filter] term forwarded but never defined:"
        , FailureCase
            "dangling section references are rejected"
            ("tests" </> "fixtures" </> "bad-section-ref.md")
            "[ref-filter] dangling section reference(s):"
        , FailureCase
            "scope end without scope begin is rejected"
            ("tests" </> "fixtures" </> "bad-decl-scope-end.md")
            "\\scopeend without matching \\scopebegin"
        , FailureCase
            "export end without export begin is rejected"
            ("tests" </> "fixtures" </> "bad-decl-export-end.md")
            "\\exportend without matching \\export{...}"
        , FailureCase
            "import of an unknown export is rejected"
            ("tests" </> "fixtures" </> "bad-decl-import.md")
            "\\import{missing} references an unknown export"
        , FailureCase
            "nested declaration exports are rejected"
            ("tests" </> "fixtures" </> "bad-decl-nested-export.md")
            "\\export{inner} started before closing active \\export{outer}"
        , FailureCase
            "unclosed declaration scope is rejected"
            ("tests" </> "fixtures" </> "bad-decl-unclosed-scope.md")
            "\\scopebegin without matching \\scopeend"
        , FailureCase
            "unclosed declaration export is rejected"
            ("tests" </> "fixtures" </> "bad-decl-unclosed-export.md")
            "\\export{dangling} without matching \\exportend"
        , FailureCase
            "mathmeta notationtype requires a declared type"
            ("tests" </> "fixtures" </> "bad-mathmeta-unknown-notation-type.md")
            "references an unknown type; add \\type{typo-type} before using it"
        , FailureCase
            "mathmeta with rejects notation directives"
            ("tests" </> "fixtures" </> "bad-mathmeta-with-define.md")
            "malformed mathmeta block"
        , FailureCase
            "mathmeta with inside nested block does not leak outward"
            ("tests" </> "fixtures" </> "bad-mathmeta-with-nested-leak.md")
            "could not infer the syntactic type of a typed notation argument"
        ]

    successFailures <-
      mapM
        (runExpectedSuccess root tmp filterBin)
        [
          ( "dependency graph tolerates a chapter outside any \\part"
          , "tests" </> "fixtures" </> "dependency-graph-partless-chapter.md"
          )
        ]

    planFailures <- runDependencyPlanTests tmp

    layoutFailures <- runDependencyLayoutCollision root tmp filterBin
    cachePathFailures <- runCachePathOverride root tmp filterBin

    parserFailures <- runParserBoundaryTests tmp filterBin

    lintFailures <- runLintTests tmp filterBin

    injectFailures <- runInjectBooklinksTests tmp filterBin

    let failures =
          concat goldenFailures
            ++ concat expectedFailures
            ++ concat successFailures
            ++ semanticExprFailures
            ++ planFailures
            ++ parserFailures
            ++ cachePathFailures
            ++ layoutFailures
            ++ lintFailures
            ++ injectFailures
    unless (null failures) $ do
      hPutStrLn stderr ""
      hPutStrLn stderr "book-filter golden tests failed:"
      forM_ failures (hPutStrLn stderr . ("  " <>))
      exitFailure

createTestDirectory :: FilePath -> IO FilePath
createTestDirectory parent = do
  (path, handle) <- openTempFile parent "book-filter-golden-"
  hClose handle
  removeFile path
  createDirectory path
  return path

-- Force and close each file before another test can overwrite the same fixture.
readTestFile :: FilePath -> IO String
readTestFile path = do
  contents <- readFile path
  _ <- evaluate (length contents)
  return contents

runGolden :: FilePath -> FilePath -> FilePath -> Golden -> IO [String]
runGolden root tmp filterBin test = do
  let input = root </> goldenInput test
      expected = root </> goldenExpected test
      actual = tmp </> takeFileName (goldenExpected test)
  (code, out, err) <- runPandoc filterBin input
  case code of
    ExitSuccess -> do
      writeFile actual out
      expectedText <- readTestFile expected
      if out == expectedText
        then pure []
        else do
          diff <- diffFiles expected actual
          pure [goldenName test <> " output differed\n" <> diff]
    ExitFailure n ->
      pure [goldenName test <> " exited with " <> show n <> "\n" <> err]

runExpectedFailure :: FilePath -> FilePath -> FailureCase -> IO [String]
runExpectedFailure root filterBin test = do
  let input = root </> failureInput test
  (code, _out, err) <- runPandoc filterBin input
  case code of
    ExitSuccess ->
      pure [failureName test <> " unexpectedly succeeded"]
    ExitFailure _ ->
      if failureExpectedStderr test `isInfixOf` err
        then pure []
        else pure [failureName test <> " failed with unexpected stderr\n" <> err]

-- A fixture that must filter without error, where the exact output is not
-- asserted (e.g. the dependency-graph layout, whose annealed positions and
-- cache hit/miss line are not portable to golden text). Runs with cwd set to
-- the temp dir so the relative `build/dependency-graph-layout.cache` the filter
-- writes lands there instead of clobbering the book's real layout cache.
runExpectedSuccess :: FilePath -> FilePath -> FilePath -> (String, FilePath) -> IO [String]
runExpectedSuccess root tmp filterBin (name, inputRel) = do
  let input = root </> inputRel
  pandocBin <- fromMaybe "pandoc" <$> lookupEnv "PANDOC_BIN"
  let process =
        (proc pandocBin [input, "-f", "markdown", "--filter", filterBin, "-t", "latex"])
          { cwd = Just tmp
          }
  (code, _out, err) <- readCreateProcessWithExitCode process ""
  case code of
    ExitSuccess -> pure []
    ExitFailure n ->
      pure [name <> " exited with " <> show n <> "\n" <> err]

-- A real filter round trip must repair even a matching cache whose nodes were
-- clamped onto the same corner, and retain the repaired layout on the next hit.
runDependencyLayoutCollision :: FilePath -> FilePath -> FilePath -> IO [String]
runDependencyLayoutCollision root tmp filterBin = do
  let directory = tmp </> "layout-collision"
      cache = directory </> "build" </> "dependency-graph-layout.cache"
      fixture = "tests" </> "fixtures" </> "dependency-graph-collision.md"
      run = runExpectedSuccess root directory filterBin ("dependency layout collision", fixture)
      positions content =
        [ (read x :: Double, read y :: Double)
        | line <- drop 1 (lines content)
        , [_node, x, y] <- [words line]
        ]
      valid points =
        length points == 6
          && and
            [ x >= 0.72 - 1e-9
                && x <= 4.94 + 1e-9
                && y >= -2.61 - 1e-9
                && y <= -0.72 + 1e-9
            | (x, y) <- points
            ]
          && and
            [ abs (x - x') >= 0.90 || abs (y - y') >= 0.65
            | (i, (x, y)) <- zip [0 :: Int ..] points
            , (x', y') <- drop (i + 1) points
            ]
  createDirectoryIfMissing True directory
  firstFailures <- run
  if not (null firstFailures)
    then pure firstFailures
    else do
      original <- readTestFile cache
      let originalValid = valid (positions original)
          collided =
            unlines
              ( take 1 (lines original)
                  ++ [node <> "\t4.94\t-2.61" | line <- drop 1 (lines original), node : _ <- [words line]]
              )
      length original `seq` writeFile cache collided
      repairedFailures <- run
      if not (null repairedFailures)
        then pure repairedFailures
        else do
          repaired <- readTestFile cache
          let repairedValid = valid (positions repaired)
          length repaired `seq` pure ()
          stableFailures <- run
          stable <- readTestFile cache
          pure
            ( stableFailures
                ++ ["fresh dependency layout contains overlapping or out-of-frame nodes" | not originalValid]
                ++ ["cached dependency layout collision was not repaired" | not repairedValid]
                ++ ["a separated cached layout changed on reuse" | stable /= repaired]
            )

runCachePathOverride :: FilePath -> FilePath -> FilePath -> IO [String]
runCachePathOverride root tmp filterBin = do
  pandoc <- fromMaybe "pandoc" <$> lookupEnv "PANDOC_BIN"
  environment <- getEnvironment
  let fixture = root </> "tests" </> "fixtures" </> "dependency-graph-collision.md"
      metadataCache = tmp </> "metadata-cache" </> "graph.cache"
      overrideCache = tmp </> "environment-cache" </> "graph.cache"
      clean = filter ((/= "DEPENDENCY_GRAPH_CACHE") . fst) environment
      command = proc pandoc [fixture, "-f", "markdown", "--filter", filterBin, "-t", "latex", "-M", "dependency-layout-cache:" <> metadataCache]
  (metaCode, _, metaErr) <- readCreateProcessWithExitCode command{cwd = Just tmp, env = Just clean} ""
  metadataExists <- doesFileExist metadataCache
  (envCode, _, envErr) <- readCreateProcessWithExitCode command{cwd = Just tmp, env = Just (("DEPENDENCY_GRAPH_CACHE", overrideCache) : clean)} ""
  overrideExists <- doesFileExist overrideCache
  pure ["dependency layout cache path override failed\n" <> metaErr <> envErr | metaCode /= ExitSuccess || envCode /= ExitSuccess || not metadataExists || not overrideExists]

-- Exercise the real parser subprocess boundary without invoking citeproc.
runParserBoundaryTests :: FilePath -> FilePath -> IO [String]
runParserBoundaryTests tmp filterBin = do
  pandoc <- fromMaybe "pandoc" <$> lookupEnv "PANDOC_BIN"
  environment <- getEnvironment
  let wrapper = tmp </> "pandoc-parser-wrapper"
      counter = tmp </> "parser-calls"
      shellQuote value = "'" <> concatMap (\c -> if c == '\'' then "'\\''" else [c]) value <> "'"
      parserProcess = (proc filterBin []){env = Just (("PANDOC_BIN", wrapper) : filter ((/= "PANDOC_BIN") . fst) environment)}
  writeFile wrapper ("#!/bin/sh\nprintf x >> " <> shellQuote counter <> "\nexec " <> shellQuote pandoc <> " \"$@\"\n")
  permissions <- getPermissions wrapper
  setPermissions wrapper permissions{executable = True}
  (_, input, _) <-
    readProcessWithExitCode
      pandoc
      ["-f", "markdown", "-t", "json"]
      "\\begin{proof}\n[@Repeated] and [@Repeated] and [@] and [@].\n\\end{proof}\n"
  (code, output, errors) <- readCreateProcessWithExitCode parserProcess input
  calls <- readTestFile counter
  let cacheFailures = ["raw citation cache did not reuse equal candidates: " <> show (length calls) <> "\n" <> errors | code /= ExitSuccess || length calls /= 2 || not ("Cite" `isInfixOf` output)]
  let glossary = tmp </> "glossary.yaml"
  writeFile glossary "terms: []\n"
  (_, glossaryInput, _) <- readProcessWithExitCode pandoc ["-f", "markdown", "-t", "json", "-M", "index-glossary:" <> glossary] "Text."
  writeFile wrapper "#!/bin/sh\nprintf 'not JSON'\n"
  (badCode, _, badErrors) <- readCreateProcessWithExitCode parserProcess glossaryInput
  let decodeFailures = ["glossary parser did not report its JSON decoding error\n" <> badErrors | badCode == ExitSuccess || not ("invalid index glossary parser output:" `isInfixOf` badErrors)]
  let fenced = tmp </> "lint-fenced-heading.md"
  writeFile fenced "````markdown\n# Example {#sec:fake}\n```\n# Still code {#sec:also-fake}\n````\nSee §{sec:fake} and §{sec:also-fake}.\n"
  (lintCode, _, lintErrors) <- readProcessWithExitCode filterBin ["lint", fenced] ""
  pure (cacheFailures ++ decodeFailures ++ ["headings inside fenced code incorrectly resolved references\n" <> lintErrors | lintCode == ExitSuccess || not ("dangling section reference sec:fake" `isInfixOf` lintErrors) || not ("dangling section reference sec:also-fake" `isInfixOf` lintErrors)])

runLintTests :: FilePath -> FilePath -> IO [String]
runLintTests tmp filterBin = do
  let okInput = tmp </> "lint-ok.md"
      badInput = tmp </> "lint-bad.md"
      fixInput = tmp </> "lint-fix.md"
      rawNotationInput = tmp </> "lint-raw-notation.md"
      rawNotationFixInput = tmp </> "lint-raw-notation-fix.md"
  writeFile okInput "short line\n"
  writeFile badInput "short line\nthis line is too long\n"
  writeFile fixInput "short line\nthis line is too long\n"
  writeFile rawNotationInput "Use $\\mathbb{N}$, $\\omega_1^{CK}$, $\\aleph_1$, $\\beth_\\alpha$, and $A \\subseteq B \\setminus C$ here.\n"
  writeFile rawNotationFixInput "Use $\\mathbb{N}$, $\\mathbb{R}$, $\\omega_1$, $\\omega_1^{CK}$, $\\aleph_0$, $\\aleph_1$, $\\beth_\\alpha$, and $A \\subsetneq B \\setminus (C \\setminus D) \\subseteq E$ here.\n"
  okFailures <- runLintSuccess filterBin okInput
  badFailures <- runLintExpectedFailure filterBin badInput
  fixFailures <- runLintFix filterBin fixInput
  rawNotationFailures <- runLintRawNotationExpectedFailure filterBin rawNotationInput
  rawNotationFixFailures <- runLintRawNotationFix filterBin rawNotationFixInput
  pure
    ( okFailures
        ++ badFailures
        ++ fixFailures
        ++ rawNotationFailures
        ++ rawNotationFixFailures
    )

runLintSuccess :: FilePath -> FilePath -> IO [String]
runLintSuccess filterBin input = do
  (code, _out, err) <-
    readProcessWithExitCode
      filterBin
      ["lint", "--max-line-length=30", input]
      ""
  case code of
    ExitSuccess -> pure []
    ExitFailure n ->
      pure ["line-length lint unexpectedly failed with " <> show n <> "\n" <> err]

runLintExpectedFailure :: FilePath -> FilePath -> IO [String]
runLintExpectedFailure filterBin input = do
  (code, _out, err) <-
    readProcessWithExitCode
      filterBin
      ["lint", "--max-line-length=12", "--max-reports=1", input]
      ""
  case code of
    ExitSuccess ->
      pure ["line-length lint unexpectedly succeeded"]
    ExitFailure _ ->
      if "[lint] source lint failed:" `isInfixOf` err
        && ":2: line length 21 > 12" `isInfixOf` err
        then pure []
        else pure ["line-length lint failed with unexpected stderr\n" <> err]

runLintFix :: FilePath -> FilePath -> IO [String]
runLintFix filterBin input = do
  (code, _out, err) <-
    readProcessWithExitCode
      filterBin
      ["lint", "--fix", "--max-line-length=12", input]
      ""
  fixed <- readTestFile input
  case code of
    ExitSuccess
      | fixed == "short line\nthis line is\ntoo long\n" ->
          pure []
      | otherwise ->
          pure ["line-length lint fix produced unexpected output\n" <> fixed]
    ExitFailure n ->
      pure ["line-length lint fix unexpectedly failed with " <> show n <> "\n" <> err]

runLintRawNotationExpectedFailure :: FilePath -> FilePath -> IO [String]
runLintRawNotationExpectedFailure filterBin input = do
  (code, _out, err) <-
    readProcessWithExitCode
      filterBin
      ["lint", "--macros=polish-space/tex/macros.tex", input]
      ""
  case code of
    ExitSuccess ->
      pure ["raw-notation lint unexpectedly succeeded"]
    ExitFailure _ ->
      if "prohibited raw notation \\mathbb{N}; use \\NN instead" `isInfixOf` err
        && "prohibited raw notation \\subseteq; use \\IncludedIn instead" `isInfixOf` err
        && "prohibited raw notation \\setminus; use \\SetDifference instead" `isInfixOf` err
        && "prohibited raw notation \\omega_1^{CK}; use \\churchKleeneOrd instead" `isInfixOf` err
        && "prohibited raw notation \\aleph_; use \\alephCard instead" `isInfixOf` err
        && "prohibited raw notation \\beth_; use \\bethCard instead" `isInfixOf` err
        then pure []
        else pure ["raw-notation lint failed with unexpected stderr\n" <> err]

runLintRawNotationFix :: FilePath -> FilePath -> IO [String]
runLintRawNotationFix filterBin input = do
  (code, _out, err) <-
    readProcessWithExitCode
      filterBin
      ["lint", "--fix", "--macros=polish-space/tex/macros.tex", input]
      ""
  fixed <- readTestFile input
  case code of
    ExitSuccess
      | fixed == "Use $\\NN$, $\\R$, $\\omegaOneOrd$, $\\churchKleeneOrd$, $\\alephNull$, $\\alephCard{1}$, $\\bethCard{\\alpha}$, and $A\n\\StrictlyIncludedIn \\SetDifference{B}{(\\SetDifference{C}{D})} \\IncludedIn E$ here.\n" ->
          pure []
      | otherwise ->
          pure ["raw-notation lint fix produced unexpected output\n" <> fixed]
    ExitFailure n ->
      pure ["raw-notation lint fix unexpectedly failed with " <> show n <> "\n" <> err]

-- The inject-booklinks subcommand consumes a sourcemap whose match.source must
-- equal the --source path, so the fixtures are generated in the temp dir (like
-- the lint tests) rather than checked in.
runInjectBooklinksTests :: FilePath -> FilePath -> IO [String]
runInjectBooklinksTests tmp filterBin = do
  happy <- happyPath
  anonymous <- anonymousPath
  structured <- structuredPath
  inlineMath <-
    expectedError "inline-math" "Value $x$ here.\n" [(7, 13)] "falls inside inline math"
  overlap <-
    expectedError "overlap" "alpha beta gamma\n" [(0, 10), (6, 16)] "overlapping source-map spans"
  skip <- skipPath
  pure (happy ++ anonymous ++ structured ++ inlineMath ++ overlap ++ skip)
 where
  sourceFile = tmp </> "inject-source.md"
  mapFile = tmp </> "inject-map.json"
  outFile = tmp </> "inject-out.md"

  -- A "skips" array injects \SkipStart{key}/\SkipEnd{key} at the span ends,
  -- coexisting with booklink entries in the same map and pass.
  writeSkipMap :: IO ()
  writeSkipMap =
    writeFile mapFile $
      unlines
        [ "{"
        , "  \"entries\": [],"
        , "  \"skips\": ["
        , "    {"
        , "      \"source\": \"" ++ sourceFile ++ "\","
        , "      \"kind\": \"block\","
        , "      \"key\": \"chap-6\","
        , "      \"startLine\": 1,"
        , "      \"startOffset\": 6,"
        , "      \"endOffset\": 23"
        , "    }"
        , "  ]"
        , "}"
        ]

  skipPath = do
    writeFile sourceFile "Kept. Skipped sentence. Kept.\n"
    writeSkipMap
    (code, _out, err) <- runInject
    case code of
      ExitFailure n -> pure ["inject-booklinks skip path failed with " <> show n <> "\n" <> err]
      ExitSuccess -> do
        result <- readTestFile outFile
        let ok =
              "Kept. \\SkipStart{chap-6}Skipped sentence.\\SkipEnd{chap-6} Kept." `isInfixOf` result
        if ok
          then pure []
          else pure ["inject-booklinks skip path produced unexpected output\n" <> result]

  runInject =
    readProcessWithExitCode
      filterBin
      ["inject-booklinks", "--sourcemap", mapFile, "--source", sourceFile, "--out", outFile]
      ""

  -- The same nested lean/booklink/match structure emitted by the Python tool.
  writeSourceMap :: [(Int, Int)] -> IO ()
  writeSourceMap spans =
    writeFile mapFile $
      unlines (["{", "  \"entries\": ["] ++ intercalate [","] (zipWith entry [0 ..] spans) ++ ["  ]", "}"])

  entry :: Int -> (Int, Int) -> [String]
  entry idx (start, end) =
    [ "    {"
    , "      \"lean\": {"
    , "        \"declName\": \"decl" ++ show idx ++ "\""
    , "      },"
    , "      \"booklink\": { \"target\": \"prose\" },"
    , "      \"match\": {"
    , "        \"status\": \"matched\","
    , "        \"source\": \"" ++ sourceFile ++ "\","
    , "        \"startOffset\": " ++ show start ++ ","
    , "        \"endOffset\": " ++ show end
    , "      }"
    , "    }"
    ]

  happyPath = do
    writeFile sourceFile "The space X is Polish.\n"
    writeSourceMap [(15, 21)]
    (code, _out, err) <- runInject
    case code of
      ExitFailure n -> pure ["inject-booklinks happy path failed with " <> show n <> "\n" <> err]
      ExitSuccess -> do
        result <- readTestFile outFile
        let ok =
              "\\BooklinkStart[entry=0]{" `isInfixOf` result
                && "}Polish" `isInfixOf` result
                && "Polish\\BooklinkEnd[entry=0]{" `isInfixOf` result
        if ok
          then pure []
          else pure ["inject-booklinks happy path produced unexpected output\n" <> result]

  structuredPath = do
    writeFile sourceFile "ABC\n"
    writeFile mapFile ("{\"entries\":[{\"match\":{\"nested\":{\"startOffset\":999},\"endOffset\":2,\"source\":\"" <> sourceFile <> "\",\"status\":\"matched\",\"startOffset\":1},\"booklink\":{\"target\":\"prose\"},\"lean\":{\"declName\":\"compact\"}}]}")
    (code, _, err) <- runInject
    result <- readTestFile outFile
    firstFailures <-
      if code == ExitSuccess && "\\BooklinkStart[entry=0]{compact}B" `isInfixOf` result
        then pure []
        else pure ["compact/reordered source map with nested metadata lost its span\n" <> err <> result]
    writeFile mapFile "{\"entries\":[{\"lean\":{},\"booklink\":{},\"match\":{\"status\":\"matched\"}}]}"
    (badCode, _, badErr) <- runInject
    schemaFailures <-
      mapM
        ( \invalid -> do
            writeFile mapFile invalid
            (schemaCode, _, schemaErr) <- runInject
            pure ["invalid source-map array schema was silently accepted\n" <> schemaErr | schemaCode == ExitSuccess || not ("invalid source map" `isInfixOf` schemaErr)]
        )
        ["{}", "{\"entries\":null}", "{\"entries\":[],\"skips\":null}"]
    pure (firstFailures ++ concat schemaFailures ++ ["incomplete matched source map was silently accepted\n" <> badErr | badCode == ExitSuccess || not ("invalid source map" `isInfixOf` badErr)])

  anonymousPath = do
    writeFile sourceFile "A B C\n"
    let anonymousEntry =
          map
            (\line -> if "\"declName\"" `isInfixOf` line then "      \"declName\": null,\n      \"anchorName\": \"anonymousInstance_Module_10\"" else line)
            (entry 1 (2, 3))
        missingEntry =
          map
            (\line -> if "\"declName\"" `isInfixOf` line then "      \"declName\": null" else line)
            (entry 0 (0, 1))
    writeFile mapFile $ unlines (["{", "  \"entries\": ["] ++ missingEntry ++ [","] ++ anonymousEntry ++ [","] ++ entry 2 (4, 5) ++ ["  ]", "}"])
    (code, _out, err) <- runInject
    case code of
      ExitFailure n -> pure ["anonymous booklink injection failed: " ++ show n ++ err]
      ExitSuccess -> do
        result <- readTestFile outFile
        if "\\BooklinkStart[entry=1]{anonymousInstance_Module_10}B" `isInfixOf` result
          && "\\BooklinkStart[entry=2]{decl2}C" `isInfixOf` result
          && not ("entry=0" `isInfixOf` result)
          then pure []
          else pure ["anonymous booklink injection lost entry identity: " ++ result]

  expectedError name source spans needle = do
    writeFile sourceFile source
    writeSourceMap spans
    (code, _out, err) <- runInject
    case code of
      ExitSuccess -> pure ["inject-booklinks " <> name <> " unexpectedly succeeded"]
      ExitFailure _ ->
        if needle `isInfixOf` err
          then pure []
          else pure ["inject-booklinks " <> name <> " failed with unexpected stderr\n" <> err]

runPandoc :: FilePath -> FilePath -> IO (ExitCode, String, String)
runPandoc filterBin input = do
  pandocBin <- fromMaybe "pandoc" <$> lookupEnv "PANDOC_BIN"
  readProcessWithExitCode
    pandocBin
    [ input
    , "-f"
    , "markdown"
    , "--filter"
    , filterBin
    , "-t"
    , "latex"
    ]
    ""

diffFiles :: FilePath -> FilePath -> IO String
diffFiles expected actual = do
  (code, out, err) <- readProcessWithExitCode "diff" ["-u", expected, actual] ""
  pure $ case code of
    ExitSuccess -> ""
    ExitFailure _ -> out <> err

isInfixOf :: (Eq a) => [a] -> [a] -> Bool
isInfixOf needle haystack =
  any (needle `prefixOf`) (tails haystack)

prefixOf :: (Eq a) => [a] -> [a] -> Bool
prefixOf [] _ = True
prefixOf _ [] = False
prefixOf (x : xs) (y : ys) = x == y && prefixOf xs ys

tails :: [a] -> [[a]]
tails [] = [[]]
tails xs@(_ : rest) = xs : tails rest
