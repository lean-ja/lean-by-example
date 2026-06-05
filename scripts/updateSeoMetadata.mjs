import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const scriptDir = path.dirname(fileURLToPath(import.meta.url));
const projectRoot = path.resolve(scriptDir, "..");
const bookDir = path.join(projectRoot, "book");
const configPath = path.join(projectRoot, "book.toml");

const configText = fs.readFileSync(configPath, "utf8");
const siteRoot = ensureTrailingSlash(readTomlString(configText, "site-url"));
const bookTitle = readTomlString(configText, "title") ?? "Lean by Example";
const defaultDescription = readTomlString(configText, "description") ?? "";
const defaultImageUrl = new URL("image/project_image.png", siteRoot).toString();

if (!fs.existsSync(bookDir)) {
  throw new Error(`Build directory does not exist: ${bookDir}`);
}

let updatedCount = 0;
let indexedCount = 0;
let skippedCount = 0;

for (const filePath of findHtmlFiles(bookDir)) {
  const relativePath = toPosixPath(path.relative(bookDir, filePath));
  const originalHtml = fs.readFileSync(filePath, "utf8");
  let html = originalHtml;

  if (relativePath === "404.html") {
    const description = extractPageDescription(html) || "お探しのページが見つかりませんでした。";
    html = upsertTag(
      html,
      /<meta\s+name=["']description["'][^>]*>/i,
      `<meta name="description" content="${escapeHtml(description)}">`,
    );
    html = upsertTag(
      html,
      /<meta\s+name=["']robots["'][^>]*>/i,
      '<meta name="robots" content="noindex">',
    );
    html = removeIndexableSeoTags(html);
    skippedCount++;
  } else if (hasNoindex(html)) {
    skippedCount++;
  } else {
    const title = extractTitle(html) ?? bookTitle;
    const description = extractPageDescription(html) || defaultDescription;
    const canonicalUrl = canonicalUrlFor(relativePath);
    const ogType = relativePath === "index.html" ? "website" : "article";

    html = upsertTag(
      html,
      /<meta\s+name=["']description["'][^>]*>/i,
      `<meta name="description" content="${escapeHtml(description)}">`,
    );
    html = upsertTag(
      html,
      /<link\s+rel=["']canonical["'][^>]*>/i,
      `<link rel="canonical" href="${escapeHtml(canonicalUrl)}">`,
    );
    html = upsertTag(
      html,
      /<meta\s+property=["']og:site_name["'][^>]*>/i,
      `<meta property="og:site_name" content="${escapeHtml(bookTitle)}">`,
    );
    html = upsertTag(
      html,
      /<meta\s+property=["']og:title["'][^>]*>/i,
      `<meta property="og:title" content="${escapeHtml(title)}">`,
    );
    html = upsertTag(
      html,
      /<meta\s+property=["']og:description["'][^>]*>/i,
      `<meta property="og:description" content="${escapeHtml(description)}">`,
    );
    html = upsertTag(
      html,
      /<meta\s+property=["']og:type["'][^>]*>/i,
      `<meta property="og:type" content="${ogType}">`,
    );
    html = upsertTag(
      html,
      /<meta\s+property=["']og:url["'][^>]*>/i,
      `<meta property="og:url" content="${escapeHtml(canonicalUrl)}">`,
    );
    html = upsertTag(
      html,
      /<meta\s+property=["']og:image["'][^>]*>/i,
      `<meta property="og:image" content="${escapeHtml(defaultImageUrl)}">`,
    );
    html = upsertTag(
      html,
      /<meta\s+property=["']og:locale["'][^>]*>/i,
      '<meta property="og:locale" content="ja_JP">',
    );
    html = upsertTag(
      html,
      /<meta\s+name=["']twitter:card["'][^>]*>/i,
      '<meta name="twitter:card" content="summary_large_image">',
    );
    html = upsertTag(
      html,
      /<meta\s+name=["']twitter:title["'][^>]*>/i,
      `<meta name="twitter:title" content="${escapeHtml(title)}">`,
    );
    html = upsertTag(
      html,
      /<meta\s+name=["']twitter:description["'][^>]*>/i,
      `<meta name="twitter:description" content="${escapeHtml(description)}">`,
    );
    html = upsertTag(
      html,
      /<meta\s+name=["']twitter:image["'][^>]*>/i,
      `<meta name="twitter:image" content="${escapeHtml(defaultImageUrl)}">`,
    );

    indexedCount++;
  }

  if (html !== originalHtml) {
    fs.writeFileSync(filePath, html);
    updatedCount++;
  }
}

console.log(
  `Updated SEO metadata in ${updatedCount} HTML files (${indexedCount} indexable pages, ${skippedCount} noindex pages).`,
);

function readTomlString(text, key) {
  const match = text.match(new RegExp(`^${escapeRegExp(key)}\\s*=\\s*"((?:\\\\.|[^"])*)"`, "m"));
  if (!match) {
    return null;
  }

  return match[1].replace(/\\([btnfr"\\])/g, (_, char) => {
    switch (char) {
      case "b":
        return "\b";
      case "t":
        return "\t";
      case "n":
        return "\n";
      case "f":
        return "\f";
      case "r":
        return "\r";
      case '"':
        return '"';
      case "\\":
        return "\\";
      default:
        return char;
    }
  });
}

function ensureTrailingSlash(url) {
  if (!url) {
    throw new Error('Missing "site-url" in book.toml');
  }

  return url.endsWith("/") ? url : `${url}/`;
}

function findHtmlFiles(dir) {
  const entries = fs.readdirSync(dir, { withFileTypes: true });
  const files = [];

  for (const entry of entries) {
    const entryPath = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      files.push(...findHtmlFiles(entryPath));
    } else if (entry.isFile() && entry.name.endsWith(".html")) {
      files.push(entryPath);
    }
  }

  return files;
}

function toPosixPath(filePath) {
  return filePath.split(path.sep).join("/");
}

function canonicalUrlFor(relativePath) {
  let urlPath = relativePath;

  if (urlPath === "index.html") {
    urlPath = "";
  } else if (urlPath.endsWith("/index.html")) {
    urlPath = urlPath.slice(0, -"index.html".length);
  }

  return new URL(encodeURI(urlPath), siteRoot).toString();
}

function hasNoindex(html) {
  return /<meta\s+name=["']robots["']\s+content=["'][^"']*\bnoindex\b[^"']*["'][^>]*>/i.test(html);
}

function extractTitle(html) {
  const match = html.match(/<title>([\s\S]*?)<\/title>/i);
  if (!match) {
    return null;
  }

  return normalizeText(decodeHtmlEntities(match[1]));
}

function extractPageDescription(html) {
  const mainHtml = extractMainHtml(html);
  const paragraphMatches = mainHtml.matchAll(/<p(?:\s[^>]*)?>([\s\S]*?)<\/p>/gi);

  for (const match of paragraphMatches) {
    const text = normalizeText(toPlainText(match[1]));
    if (text.length >= 10) {
      return truncateDescription(text);
    }
  }

  return "";
}

function extractMainHtml(html) {
  const startMarker = '<div class="content-wrap">';
  const endMarker = '<div class="sidetoc">';
  const start = html.indexOf(startMarker);

  if (start === -1) {
    return html;
  }

  const end = html.indexOf(endMarker, start);
  if (end === -1) {
    return html.slice(start + startMarker.length);
  }

  return html.slice(start + startMarker.length, end);
}

function toPlainText(fragment) {
  return decodeHtmlEntities(
    fragment
      .replace(/<script\b[\s\S]*?<\/script>/gi, " ")
      .replace(/<style\b[\s\S]*?<\/style>/gi, " ")
      .replace(/<br\s*\/?>/gi, " ")
      .replace(/<[^>]+>/g, " "),
  );
}

function decodeHtmlEntities(text) {
  const namedEntities = {
    amp: "&",
    apos: "'",
    gt: ">",
    lt: "<",
    nbsp: " ",
    quot: '"',
  };

  return text.replace(/&(#x[0-9a-fA-F]+|#\d+|[a-zA-Z][a-zA-Z0-9]+);/g, (match, entity) => {
    if (entity.startsWith("#x")) {
      return String.fromCodePoint(Number.parseInt(entity.slice(2), 16));
    }
    if (entity.startsWith("#")) {
      return String.fromCodePoint(Number.parseInt(entity.slice(1), 10));
    }

    return namedEntities[entity] ?? match;
  });
}

function normalizeText(text) {
  return text
    .replace(/\s+/g, " ")
    .replace(/\s+([、。！？])/g, "$1")
    .replace(/([、。！？])\s+/g, "$1")
    .trim();
}

function truncateDescription(text) {
  const maxLength = 160;
  const chars = Array.from(text);

  if (chars.length <= maxLength) {
    return text;
  }

  return `${chars.slice(0, maxLength - 3).join("").trimEnd()}...`;
}

function upsertTag(html, pattern, tag) {
  if (pattern.test(html)) {
    return html.replace(pattern, tag);
  }

  return html.replace(/<\/head>/i, `        ${tag}\n    </head>`);
}

function removeIndexableSeoTags(html) {
  return html
    .replace(/\n?\s*<link\s+rel=["']canonical["'][^>]*>/gi, "")
    .replace(/\n?\s*<meta\s+property=["']og:[^"']+["'][^>]*>/gi, "")
    .replace(/\n?\s*<meta\s+name=["']twitter:[^"']+["'][^>]*>/gi, "");
}

function escapeHtml(value) {
  return value
    .replace(/&/g, "&amp;")
    .replace(/"/g, "&quot;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;");
}

function escapeRegExp(value) {
  return value.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}
