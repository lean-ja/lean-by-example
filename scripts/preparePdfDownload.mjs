import { createHash } from "node:crypto";
import fs from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";

const projectRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const pdfName = "lean-by-example.pdf";
const metadataName = "pdf.json";

function validatePdf(pdf) {
  if (pdf.subarray(0, 5).toString() !== "%PDF-" || !pdf.subarray(-1024).includes("%%EOF")) {
    throw new Error("Invalid or incomplete PDF");
  }
}

function digest(pdf) {
  return createHash("sha256").update(pdf).digest("hex");
}

function validateBundle(pdf, metadata) {
  validatePdf(pdf);
  if (!metadata.available
      || typeof metadata.sourceSha !== "string"
      || !/^(?:[a-f0-9]{40}|local)$/.test(metadata.sourceSha)
      || typeof metadata.builtAt !== "string"
      || !Number.isFinite(Date.parse(metadata.builtAt))
      || metadata.sha256 !== digest(pdf)) {
    throw new Error("PDF metadata does not match the PDF");
  }
  return { pdf, metadata };
}

async function writeMetadata(directory, metadata) {
  await fs.writeFile(path.join(directory, metadataName), `${JSON.stringify(metadata, null, 2)}\n`);
}

export async function createPdfArtifact({ pdfPath, artifactDir, sourceSha }) {
  const pdf = await fs.readFile(pdfPath);
  const metadata = {
    available: true,
    sourceSha,
    builtAt: new Date().toISOString(),
    sha256: digest(pdf),
  };
  validateBundle(pdf, metadata);
  await fs.mkdir(artifactDir, { recursive: true });
  await fs.writeFile(path.join(artifactDir, pdfName), pdf);
  await writeMetadata(artifactDir, metadata);
  return metadata;
}

async function readArtifact(artifactDir, sourceSha) {
  const metadata = JSON.parse(await fs.readFile(path.join(artifactDir, metadataName), "utf8"));
  const pdf = await fs.readFile(path.join(artifactDir, pdfName));
  const bundle = validateBundle(pdf, metadata);
  if (metadata.sourceSha !== sourceSha) {
    throw new Error("PDF artifact was built from a different commit");
  }
  return bundle;
}

export async function preparePdfDownload({
  bookDir,
  artifactDir,
  sourceSha,
  warn = console.warn,
}) {
  // 後続の PDF 処理が失敗しても、存在しない PDF へのリンクを表示しない。
  await writeMetadata(bookDir, { available: false });
  await fs.rm(path.join(bookDir, pdfName), { force: true });

  let bundle;
  try {
    bundle = await readArtifact(artifactDir, sourceSha);
  } catch (error) {
    warn(`Current PDF unavailable: ${error.message}`);
  }

  if (!bundle) return { available: false };

  await fs.writeFile(path.join(bookDir, pdfName), bundle.pdf);
  await writeMetadata(bookDir, bundle.metadata);
  return bundle.metadata;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const artifactDir = path.join(projectRoot, "pdf-artifact");
  const sourceSha = process.env.GITHUB_SHA || "local";
  if (process.argv[2] === "artifact") {
    await createPdfArtifact({
      pdfPath: path.join(projectRoot, "typst/book.pdf"),
      artifactDir,
      sourceSha,
    });
  } else if (process.argv[2] === "site") {
    const metadata = await preparePdfDownload({
      bookDir: path.join(projectRoot, "book"),
      artifactDir,
      sourceSha,
    });
    const message = metadata.available
      ? "Publishing the PDF built from the current commit."
      : "PDF preparation failed; HTML deployment can continue with PDF download disabled.";
    console.log(message);
    if (!metadata.available && process.env.GITHUB_ACTIONS) {
      console.log(`::warning::${message}`);
    }
    if (process.env.GITHUB_STEP_SUMMARY) {
      await fs.appendFile(process.env.GITHUB_STEP_SUMMARY, `${message}\n`);
    }
  } else {
    throw new Error("Usage: node scripts/preparePdfDownload.mjs artifact|site");
  }
}
