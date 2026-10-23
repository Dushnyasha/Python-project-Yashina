"""StudyFlow, календарь учебных дедлайнов и оценок."""

import calendar
import copy
import html
from html.parser import HTMLParser
import io
import json
import os
from pathlib import Path
import posixpath
import queue
import re
import shutil
import threading
import unicodedata
import urllib.request
import uuid
import webbrowser
import xml.etree.ElementTree as ET
import zipfile
from datetime import date, datetime, timedelta, timezone


DATA_FILE = Path(__file__).resolve().with_name("studyflow_data.json")
STATUSES = ["Не начато", "В процессе", "Готово"]
SOURCE_LABELS = {"deadlines": "Дедлайны", "grades": "Оценки"}
DISCUSSION_MARKERS = ["можно было прислать", "подскажите, пожалуйста"]
MSK = timezone(timedelta(hours=3))
MONTHS = ["января", "февраля", "марта", "апреля", "мая", "июня",
          "июля", "августа", "сентября", "октября", "ноября", "декабря"]
MONTH_NAMES = ["Январь", "Февраль", "Март", "Апрель", "Май", "Июнь",
               "Июль", "Август", "Сентябрь", "Октябрь", "Ноябрь", "Декабрь"]
MATH = "Математика для анализа данных"
PYTHON = "Программирование на Python"
MARKETING = "Маркетинг в цифровой среде"
RESEARCH = "Маркетинговый анализ и исследования"
MENTOR = "Семинар наставника"

def default_settings():
    weights = {}
    for subject, count, weight, exam in [(PYTHON, 3, .15, .35), (MARKETING, 3, .15, .35), (RESEARCH, 5, .10, .30)]:
        weights[subject] = {"ДЗ " + str(i): weight for i in range(1, count + 1)}
        weights[subject].update({"Проект": .20, "Экзамен": exam})
    weights[MATH] = {"ДЗ " + str(i): .011 for i in range(1, 23)}
    weights[MATH].update({"Лабораторная 1": .10, "Лабораторная 2": .10, "Лабораторная 3": .10, "Контрольная 1": .15,
                          "Контрольная 2": .15, "Экзамен": .16})
    weights[MENTOR] = {"ДЗ " + str(i): 0 for i in range(1, 5)}
    return {
        "student_name": "", "sync_on_start": False, "grades_sheet": "", "deadlines_sheet": "",
        "chat_key": "ИИМУП 2026-2028",
        "subject_aliases": {
            MATH: ["математика", "матан", "матем. для анализа данных", "адаптационный курс по математике"],
            PYTHON: ["python", "питон", "программирование"],
            MARKETING: ["маркетинг в цифровой среде", "маркетинг в цифр.среде"],
            RESEARCH: ["маркетинговый анализ", "маркетинговый анализ и исследов"],
            MENTOR: ["семинар наставника"]
        },
        "task_markers": ["домашнее задание", "домашняя работа", "дз", "домашка",
                         "проект", "задание", "сдать", "заполнить", "подтвердить", "активировать", "заявку", "сформировать", "загрузки документов"],
        "deadline_markers": ["дедлайн", "срок сдачи", "сдать до", "принимается до", "форма открыта до", "до", "к"],
        "exclude_markers": ["пример: дедлайн", "разбор домашней работы", "разбор дз",
                            "какой дедлайн", "когда будет дедлайн", "какие дедлайны"] + DISCUSSION_MARKERS,
        "weights": weights
    }

def normalize_text(text):
    text = unicodedata.normalize("NFKC", str(text).replace("№", "#")).lower().replace("ё", "е")
    text = text.replace("\ufe0f", "").replace("\u20e3", "").replace("\xa0", " ")
    text = re.sub(r"\bcентябр", "сентябр", text)
    return re.sub(r"\s+", " ", text).strip()

def normalize_name(text):
    return tuple(sorted(re.findall(r"[а-яa-z]+", normalize_text(text))))

def validate_settings(settings):
    if not isinstance(settings, dict):
        raise ValueError("Настройки должны быть JSON-объектом.")
    for key in ["task_markers", "deadline_markers", "exclude_markers"]:
        if not isinstance(settings.get(key), list) or not all(isinstance(x, str) and x.strip() for x in settings[key]):
            raise ValueError(key + ": нужен список непустых строк.")
    aliases = settings.get("subject_aliases")
    if not isinstance(aliases, dict) or not aliases:
        raise ValueError("subject_aliases: нужен словарь предметов.")
    for subject, names in aliases.items():
        if not isinstance(subject, str) or not isinstance(names, list) or not all(isinstance(n, str) and n.strip() for n in names):
            raise ValueError("Неверный словарь псевдонимов предметов.")
    weights = settings.get("weights")
    if not isinstance(weights, dict):
        raise ValueError("weights: нужен словарь весов.")
    for subject, works in weights.items():
        if not isinstance(works, dict) or not works or not all(isinstance(w, str) and w.strip() and isinstance(v, (int, float)) and not isinstance(v, bool) and 0 <= v <= 1 for w, v in works.items()):
            raise ValueError("Веса работ должны быть числами от 0 до 1.")
    if not isinstance(settings.get("sync_on_start"), bool):
        raise ValueError("sync_on_start: нужно true или false.")
    for key in ["student_name", "chat_key", "grades_sheet", "deadlines_sheet"]:
        if not isinstance(settings.get(key), str):
            raise ValueError(key + ": нужна строка.")

def new_state():
    return {"version": 1, "data_revision": 2, "settings": default_settings(), "tasks": [], "grades": {},
            "reported_grades": {}, "sync": {}, "notes": {}, "imports": [], "deleted_tasks": []}

def load_data(path=DATA_FILE):
    path = Path(path)
    if not path.exists():
        return new_state()
    try:
        state = json.loads(path.read_text(encoding="utf-8"))
        validate_settings(state["settings"])
        if (state.get("version") != 1 or not isinstance(state.get("tasks"), list) or
                any(not isinstance(state.get(key), dict) for key in ["grades", "reported_grades", "sync"])):
            raise ValueError("Неизвестный формат данных.")
        for task in state["tasks"]:
            date.fromisoformat(task["deadline"])
            if task["status"] not in STATUSES or not isinstance(task.get("sources"), list):
                raise ValueError("Повреждена запись задания.")
            for key in ["id", "title", "subject", "work", "time"]:
                if not isinstance(task.get(key), str):
                    raise ValueError("Повреждено поле задания: " + key)
            if task["time"] and not re.fullmatch(r"(?:[01]\d|2[0-3]):[0-5]\d", task["time"]):
                raise ValueError("Неверное время задания.")
        for subjects in state["grades"].values():
            for works in subjects.values():
                for record in works.values():
                    for key in ["manual", "imported"]:
                        if record.get(key) is not None and (not isinstance(record[key], (int, float)) or
                                                          isinstance(record[key], bool) or parse_grade(record[key]) is None):
                            raise ValueError("Некорректная сохранённая оценка.")
        for key, default in [("notes", {}), ("imports", []), ("deleted_tasks", [])]:
            state.setdefault(key, default)
            if not isinstance(state[key], type(default)):
                raise ValueError("Повреждено поле: " + key)
        for day, text in state["notes"].items():
            date.fromisoformat(day)
            if not isinstance(text, str):
                raise ValueError("Повреждена заметка.")
        if state.get("data_revision") != 2:
            for marker in DISCUSSION_MARKERS:
                if marker not in state["settings"]["exclude_markers"]:
                    state["settings"]["exclude_markers"].append(marker)
            repair_deadlines(state)
            state["data_revision"] = 2
            save_data(state, path)
        if complete_graded_tasks(state):
            save_data(state, path)
        return state
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as error:
        raise ValueError("Не удалось прочитать " + str(path) + ". Файл не перезаписан. "
                         "При необходимости восстановите копию .json.bak. Причина: " + str(error)) from error

def save_data(state, path=DATA_FILE):
    # Сначала записываем временный файл целиком, затем атомарно заменяем основной.
    path = Path(path)
    temporary = path.with_suffix(".json.tmp")
    with temporary.open("w", encoding="utf-8") as file:
        json.dump(state, file, ensure_ascii=False, indent=2, allow_nan=False)
        file.flush()
        os.fsync(file.fileno())
    if path.exists():
        shutil.copy2(path, str(path) + ".bak")
    os.replace(temporary, path)

def message_file_order(name):
    filename = Path(name).name.lower()
    number = re.search(r"\d+", filename)
    page = 1
    if number:
        page = int(number.group())
    return str(Path(name).parent), page

def telegram_files(names):
    html_files, json_files = [], []
    for name in names:
        filename = Path(name).name.lower()
        if re.fullmatch(r"messages\d*\.html", filename):
            html_files.append(name)
        elif filename == "result.json":
            json_files.append(name)
    files = html_files or json_files
    if not files:
        raise ValueError("Нет messages*.html или result.json.")
    return sorted(files, key=message_file_order)

def find_links(text, links=None):
    result = {}
    candidates = list(links or []) + re.findall(r"https?://[^\s<>\"]+", text)
    for link in candidates:
        link = html.unescape(link).strip().rstrip(".,;!?)")
        if re.match(r"^https?://", link, re.I):
            result[link] = None
    return list(result)

def read_html(text, chat_key):
    parser = HTMLParser(convert_charrefs=True)
    messages = []
    depth = 0
    current = None
    parts = []
    capture = {}

    def finish_message():
        if current is not None:
            current["text"] = "".join(parts).strip()
            current["links"] = find_links(current["text"], current["links"])
            messages.append(current)

    def start(tag, attributes):
        nonlocal current, parts, depth
        attributes = dict(attributes)
        classes = attributes.get("class", "").split()
        if tag == "div":
            depth += 1
            if "message" in classes:
                finish_message()
                current = {"id": attributes.get("id", ""), "date": "", "text": "", "links": [], "reply": "",
                           "chat": chat_key, "service": "service" in classes}
                parts = []
                capture.clear()
            if current is not None:
                if "date" in classes:
                    current["date"] = attributes.get("title", "")
                if classes == ["text"]:
                    capture["text"] = depth
                if "reply_to" in classes:
                    capture["reply"] = depth
                if current["service"] and "body" in classes:
                    capture["service"] = depth
        if current is not None and tag == "a":
            link = attributes.get("href", "")
            if "reply" in capture:
                match = re.search(r"(?:go_to_)?message(-?\d+)$", link)
                if match:
                    current["reply"] = "message" + match.group(1)
            if "text" in capture and link:
                current["links"].append(link)
        if ("text" in capture or "service" in capture) and tag == "br":
            parts.append("\n")

    def end(tag):
        nonlocal depth
        if tag == "div" and depth:
            for role in list(capture):
                if capture[role] == depth:
                    del capture[role]
            depth -= 1

    def data(value):
        if "text" in capture or "service" in capture:
            parts.append(value)

    parser.handle_starttag = start
    parser.handle_endtag = end
    parser.handle_data = data
    parser.feed(text)
    parser.close()
    finish_message()
    if not messages:
        raise ValueError("HTML не содержит ожидаемых блоков сообщений Telegram.")
    return messages

def read_json_export(text, chat_key):
    content = json.loads(text)
    if not isinstance(content, dict):
        raise ValueError("Нужен JSON-экспорт Telegram Desktop.")
    chats = content.get("chats", {})
    if "messages" in content:
        chats = [content]
    elif isinstance(chats, dict):
        chats = chats.get("list", [])
    else:
        chats = []
    if not chats:
        raise ValueError("В JSON нет списка messages или chats.list.")
    result = []
    for chat in chats:
        if not isinstance(chat, dict) or not isinstance(chat.get("messages"), list):
            continue
        identity = chat_key
        if len(chats) > 1:
            identity += ":" + str(chat.get("id") or chat.get("name", ""))
        for message in chat["messages"]:
            if not isinstance(message, dict):
                continue
            parts = message.get("text", "")
            if isinstance(parts, str):
                parts = [parts]
            if not isinstance(parts, list):
                parts = []
            texts, links = [], []
            for index, part in enumerate(parts + message.get("text_entities", [])):
                if isinstance(part, dict):
                    if part.get("href"):
                        links.append(part["href"])
                    part = str(part.get("text", ""))
                if index < len(parts) and isinstance(part, str):
                    texts.append(part)
            text_parts = "".join(texts)
            if message.get("action") == "topic_created":
                text_parts = "created topic «" + str(message.get("title", "")) + "»"
            message_id = message.get("id", "")
            reply = message.get("reply_to_message_id", "")
            if message_id != "":
                message_id = "message" + str(message_id)
            if reply != "":
                reply = "message" + str(reply)
            result.append({"id": message_id, "date": message.get("date", ""), "text": text_parts,
                           "links": find_links(text_parts, links), "reply": reply, "chat": identity,
                           "service": message.get("type") != "message"})
    return result

def read_telegram_export(paths, settings):
    messages = []
    errors = []
    count = 0

    def process(name, raw):
        nonlocal count
        try:
            text = raw.decode("utf-8-sig")
            if str(name).lower().endswith(".json"):
                items = read_json_export(text, settings["chat_key"])
            else:
                items = read_html(text, settings["chat_key"])
            messages.extend(items)
            count += 1
        except (ValueError, TypeError, KeyError) as error:
            errors.append(str(name) + ": " + str(error))

    for path in paths:
        path = Path(path)
        try:
            if path.is_dir():
                files = telegram_files(p for p in path.rglob("*") if p.is_file())
                for file in files:
                    process(str(file), file.read_bytes())
            elif path.suffix.lower() == ".zip":
                with zipfile.ZipFile(path) as archive:
                    files = telegram_files(archive.namelist())
                    for name in files:
                        info = archive.getinfo(name)
                        if info.file_size > 40 * 1024 * 1024:
                            errors.append(name + ": файл больше 40 МБ, разбейте экспорт по периоду.")
                            continue
                        process(name, archive.read(name))
            elif path.suffix.lower() in [".html", ".json"]:
                process(str(path), path.read_bytes())
            else:
                raise ValueError("Выберите ZIP, JSON или messages*.html.")
        except (OSError, ValueError, zipfile.BadZipFile, RuntimeError) as error:
            errors.append(path.name + ": " + str(error))
    return messages, count, errors

def find_subject(text, settings):
    text = normalize_text(text)
    for subject, aliases in settings["subject_aliases"].items():
        for alias in [subject] + aliases:
            if normalize_text(alias) in text:
                return subject
    return "Не определён"

def source_datetime(value):
    try:
        value = str(value)
        match = re.match(r"(\d{2}\.\d{2}\.\d{4}) (\d{2}:\d{2}:\d{2})", value)
        if match:
            return datetime.strptime(" ".join(match.groups()), "%d.%m.%Y %H:%M:%S")
        return datetime.fromisoformat(value.replace("Z", "+00:00")).replace(tzinfo=None)
    except ValueError:
        return None

def has_marker(text, markers, deadline=False):
    for marker in markers:
        marker = normalize_text(marker)
        pattern = r"(?<!\w)" + re.escape(marker) + r"(?!\w)"
        if deadline and marker in ["до", "к"]:
            pattern += r"\s+(?:\d{1,2}|сегодня|завтра|послезавтра|понедельник|вторник|сред|четверг|пятниц|суббот|воскресень)"
        if re.search(pattern, text):
            return True
    return False

def is_deadline_message(text, settings):
    text = normalize_text(text)
    if any(normalize_text(marker) in text for marker in settings["exclude_markers"]):
        return False
    return (has_marker(text, settings["task_markers"]) and
            has_marker(text, settings["deadline_markers"], deadline=True))

def find_deadline_date(text, message_date):
    text = normalize_text(text)
    base = source_datetime(message_date)
    # Берём дату из строки с дедлайном, чтобы не спутать с датой занятия.
    marker = re.search(r"дедлайн|срок сдачи|принимается до|форма открыта до", text)
    search_text = text
    if marker:
        search_text = text[marker.end():]
    patterns = [r"(?<![\w/])(\d{1,2})[./](\d{1,2})(?:[./](\d{4}))?(?![\w/])",
                r"(?<!\w)(\d{1,2})\s+(" + "|".join(MONTHS) + r")(?:\s+(\d{4}))?(?!\w)"]
    for pattern in patterns:
        match = re.search(pattern, search_text)
        if not match:
            continue
        day, month, year = match.groups()
        if month in MONTHS:
            month = MONTHS.index(month) + 1
        month = int(month)
        if not year and base is None:
            return None
        year = int(year or base.year)
        try:
            result = date(year, month, int(day))
            # Переход декабрь -> январь. Небольшую просрочку не переносим на год.
            if not match.group(3) and base.month == 12 and month in (1, 2):
                result = date(year + 1, month, int(day))
            return result.isoformat()
        except ValueError:
            return None
    if base is None:
        return None
    for word, days in [("послезавтра", 2), ("завтра", 1), ("сегодня", 0)]:
        if re.search(r"\b" + word + r"\b", search_text):
            return (base.date() + timedelta(days=days)).isoformat()
    weekdays = ["понедельник", "вторник", "сред", "четверг", "пятниц", "суббот", "воскресень"]
    for weekday, word in enumerate(weekdays):
        if re.search(r"\b(?:до|к)\s+" + word + r"[а-я]*\b", search_text):
            days = (weekday - base.weekday()) % 7
            return (base.date() + timedelta(days=days)).isoformat()
    return None

def work_numbers(text):
    text = normalize_text(text)
    names = r"(?:домашн(?:ее задание|яя работа)|дз|домашка)"
    result = []
    for pattern in [r"\b" + names + r"\s*[№#]?\s*(\d{1,2})\b", r"\b(\d{1,2})\s*" + names + r"\b"]:
        for number in re.findall(pattern, text):
            if int(number) not in result:
                result.append(int(number))
    ordinals = {"первое": 1, "второе": 2, "третье": 3, "четвертое": 4, "пятое": 5}
    for word, number in ordinals.items():
        if word + " домашнее задание" in text and number not in result:
            result.append(number)
    return result

def infer_work(text):
    text = normalize_text(text)
    # Заявка на проект и подготовка к ДЗ сами по себе не являются оценочными работами.
    if any(word in text for word in ["заявку", "подготовитель", "сформировать", "создайте", "заполните"]):
        return ""
    numbers = work_numbers(text)
    if numbers:
        return "ДЗ " + str(numbers[0])
    for word, name in [("лабораторн", "Лабораторная"), ("контрольн", "Контрольная")]:
        match = re.search(word + r"[а-я\s]*[№#]?\s*(\d+)", text)
        if match:
            return name + " " + match.group(1)
    if "экзамен" in text:
        return "Экзамен"
    if "проект" in text:
        return "Проект"
    return ""

def split_task_blocks(text, settings, message_date):
    blocks = []
    current = []
    subject_seen = False
    heading = ""
    for line in text.splitlines():
        subject = find_subject(line, settings)
        is_heading = subject != "Не определён" and len(normalize_text(line)) < 85
        current_text = "\n".join(current)
        numbered = bool(work_numbers(line)) or bool(re.search(r"(?:лабораторн|контрольн)[а-я\s]*[№#]?\s*\d+", normalize_text(line)))
        completed = is_deadline_message(current_text, settings) and find_deadline_date(current_text, message_date)
        if completed and ((is_heading and subject_seen) or numbered):
            blocks.append("\n".join(current))
            current = []
            if not is_heading and heading:
                current.append(heading)
        if is_heading:
            heading = subject
        current.append(line)
        subject_seen = subject_seen or is_heading
    if current:
        blocks.append("\n".join(current))
    result = []
    for block in blocks:
        numbered = [line for line in block.splitlines() if is_deadline_message(line, settings) and
                    find_deadline_date(line, message_date)]
        if len(numbered) > 1:
            heading = find_subject(block, settings)
            if heading == "Не определён":
                heading = ""
            for line in numbered:
                result.append(heading + "\n" + line)
        else:
            result.append(block)
    return result

def create_deadlines(message, subject, settings):
    result = []
    for block in split_task_blocks(message["text"], settings, message["date"]):
        if not is_deadline_message(block, settings):
            continue
        deadline = find_deadline_date(block, message["date"])
        if not deadline:
            continue
        block_subject = find_subject(block, settings)
        if block_subject == "Не определён":
            block_subject = subject
        time_text = re.split(r"дедлайн|срок сдачи", normalize_text(block))[-1]
        time_match = re.search(r"\b([01]?\d|2[0-3]):([0-5]\d)\b", time_text)
        time = ""
        if time_match:
            time = "%02d:%s" % (int(time_match.group(1)), time_match.group(2))
        numbers = work_numbers(block)
        # «Подготовительный этап к домашним заданиям» не превращается в ДЗ.
        works = ["ДЗ " + str(n) for n in numbers] or [infer_work(block)]
        for work in works:
            if work:
                title = work
            else:
                lines = [line.strip(" 📎🔗👁️➕•") for line in block.splitlines() if line.strip()]
                candidates = [line for line in lines if find_subject(line, settings) == "Не определён"
                              and "дедлайн" not in normalize_text(line)
                              and not line.startswith(("http", "Форма", "описание"))]
                actionable = [line for line in lines if has_marker(normalize_text(line), settings["task_markers"])]
                if candidates and normalize_text(candidates[0]).startswith(("добрый", "коллеги", "привет", "здравствуйте")):
                    candidates = actionable or candidates[1:]
                title = "Учебная задача"
                if candidates:
                    title = candidates[0][:110]
            item = work or normalize_text(title)
            source = {"kind": message.get("kind", "telegram"), "chat": message["chat"], "message_id": message["id"],
                      "item": item, "date": message["date"], "text": message["text"], "deadline": deadline,
                      "time": time, "links": message["links"]}
            result.append({"id": uuid.uuid4().hex, "title": title, "subject": block_subject,
                           "work": work, "deadline": deadline, "time": time,
                           "links": message["links"], "status": "Не начато", "sources": [source]})
    return result

def extract_deadlines(messages, settings):
    index = {(m["chat"], m["id"]): m for m in messages if m["id"]}
    result = []
    unresolved = []
    seen = set()
    for message in messages:
        if message["service"] or not message["text"]:
            continue
        identity = (message["chat"], message["id"])
        if message["id"] and identity in seen:
            continue
        seen.add(identity)
        subject = find_subject(message["text"], settings)
        reply = message["reply"]
        visited = set()
        while subject == "Не определён" and reply and reply not in visited:
            visited.add(reply)
            parent = index.get((message["chat"], reply))
            if not parent:
                break
            subject = find_subject(parent["text"], settings)
            reply = parent["reply"]
        tasks = create_deadlines(message, subject, settings)
        if not tasks and is_deadline_message(message["text"], settings):
            unresolved.append(message["id"] + ": не удалось однозначно извлечь дату")
        result.extend(tasks)
    return result, unresolved

def source_key(source):
    if not source.get("message_id"):
        return None
    return (source["kind"], source["chat"], source["message_id"], normalize_text(source["item"]))

def make_deadline_key(task):
    title = task["work"] or task["title"]
    return (task["subject"], normalize_text(title), task["deadline"])

def choose_task_source(task):
    sources = task["sources"]
    # Синхронизированная таблица имеет приоритет для даты над старым экспортом.
    sheets = [s for s in sources if s["kind"] == "sheet"]
    candidates = sheets or sources
    latest = max(enumerate(candidates), key=lambda pair: (source_datetime(pair[1]["date"]) or datetime.min, pair[0]))[1]
    task["deadline"] = latest["deadline"]
    explicit_times = [s for s in candidates if s.get("time")]
    latest_time = max(enumerate(explicit_times), key=lambda pair: (source_datetime(pair[1]["date"]) or datetime.min, pair[0]), default=(0, {}))[1]
    task["time"] = latest_time.get("time", "")
    task["links"] = find_links("", [link for s in sources for link in s["links"]])
    task.update(task.get("manual", {}))

def numbered_work_key(task):
    if task["subject"] != "Не определён" and re.fullmatch(r"(?:ДЗ|Лабораторная|Контрольная) \d+", task["work"]):
        return task["subject"], task["work"]

def nearby_deadlines(first, second):
    return abs((date.fromisoformat(first) - date.fromisoformat(second)).days) <= 120

def merge_deadlines(old_tasks, new_tasks):
    tasks = copy.deepcopy(old_tasks)
    by_source, by_content, by_day, by_work = {}, {}, {}, {}
    existing = 0

    def index_task(position):
        task = tasks[position]
        for source in task["sources"]:
            key = source_key(source)
            if key is not None:
                by_source.setdefault(key, position)
        by_content.setdefault(make_deadline_key(task), set()).add(position)
        by_day.setdefault((task["subject"], task["deadline"]), set()).add(position)
        work_key = numbered_work_key(task)
        if work_key:
            by_work.setdefault(work_key, set()).add(position)

    for position in range(len(tasks)):
        index_task(position)
    for incoming in new_tasks:
        incoming_source = incoming["sources"][0]
        key = source_key(incoming_source)
        position = by_source.get(key)
        content_key = make_deadline_key(incoming)
        day_key = (incoming["subject"], incoming["deadline"])
        if position is None and incoming["subject"] != "Не определён":
            matches = by_content.get(content_key, set())
            if matches and (incoming["work"] or len(normalize_text(incoming["title"])) > 15):
                position = min(matches)
        if position is None and numbered_work_key(incoming):
            matches = []
            for candidate in by_work.get(numbered_work_key(incoming), set()):
                if nearby_deadlines(tasks[candidate]["deadline"], incoming["deadline"]):
                    matches.append(candidate)
            if len(matches) == 1:
                position = matches[0]
        if position is None and incoming["links"]:
            # Для репоста проверяем только задачи того же предмета и дня.
            referenced = set()
            for link in incoming["links"]:
                match = re.search(r"https://t\.me/c/\d+/(?:\d+/)?(\d+)$", link)
                if match:
                    referenced.add("message" + match.group(1))
            matches = []
            incoming_links = set(incoming["links"])
            for candidate in by_day.get(day_key, set()):
                task = tasks[candidate]
                if task["work"] and incoming["work"] and task["work"] != incoming["work"]:
                    continue
                shared_links = incoming_links.intersection(task["links"])
                same_link = any(len(link.split("/")) >= 5 for link in shared_links)
                explicit_reference = any(s["message_id"] in referenced for s in task["sources"])
                if explicit_reference or (same_link and (not task["work"] or not incoming["work"])):
                    matches.append(candidate)
            if len(matches) == 1:
                position = matches[0]
        if position is not None and incoming.get("manual"):
            for field, value in incoming["manual"].items():
                if field in tasks[position].get("manual", {}) and tasks[position]["manual"][field] != value:
                    position = None
                    break
        if position is None:
            tasks.append(copy.deepcopy(incoming))
            index_task(len(tasks) - 1)
            continue
        existing += 1
        target = tasks[position]
        by_content[make_deadline_key(target)].discard(position)
        by_day[(target["subject"], target["deadline"])].discard(position)
        work_key = numbered_work_key(target)
        if work_key:
            by_work[work_key].discard(position)
        for incoming_source in incoming["sources"]:
            for source_position, source in enumerate(target["sources"]):
                if source_key(incoming_source) is not None and source_key(source) == source_key(incoming_source):
                    old_date = source_datetime(source["date"]) or datetime.min
                    new_date = source_datetime(incoming_source["date"]) or datetime.min
                    fields = ["text", "deadline", "time", "links"]
                    if new_date >= old_date and any(source.get(field) != incoming_source.get(field) for field in fields):
                        replacement = copy.deepcopy(incoming_source)
                        history = copy.deepcopy(source.get("history", []))
                        if source["text"] != replacement["text"]:
                            history.append({"text": source["text"], "date": source["date"]})
                        if history:
                            replacement["history"] = history
                        target["sources"][source_position] = replacement
                    break
            else:
                target["sources"].append(copy.deepcopy(incoming_source))
        if target["subject"] == "Не определён":
            target["subject"] = incoming["subject"]
        if not target["work"]:
            if incoming["work"]:
                target["work"] = incoming["work"]
                target["title"] = incoming["title"]
            elif len(incoming_source["text"]) < len(target["sources"][0]["text"]):
                target["title"] = incoming["title"]
        choose_task_source(target)
        index_task(position)
    return tasks, len(tasks) - len(old_tasks), existing


def import_view(state):
    tasks = {}
    for task in state["tasks"]:
        tasks[task["id"]] = task
    return {"tasks": tasks, "grades": state["grades"], "reported_grades": state["reported_grades"], "sync": state["sync"]}

def import_changes(before, after, path=()):
    changes = []
    for key in dict.fromkeys(list(before) + list(after)):
        old, new = before.get(key), after.get(key)
        location = path + (key,)
        added_task = len(location) == 2 and location[0] == "tasks" and key not in before
        if isinstance(new, dict) and (isinstance(old, dict) or key not in before) and not added_task:
            changes.extend(import_changes(old or {}, new, location))
        elif old != new or (key in before) != (key in after):
            changes.append([list(location), key in before, old, key in after, copy.deepcopy(new)])
    return changes

def record_import(state, label, action):
    before = copy.deepcopy(import_view(state))
    result = action()
    complete_graded_tasks(state)
    changes = import_changes(before, import_view(state))
    state.setdefault("imports", []).append({"label": label, "time": datetime.now(MSK).isoformat(timespec="seconds"),
                                            "changes": changes})
    return result

def undo_import(state):
    history = state.setdefault("imports", [])
    if not history:
        raise ValueError("Нет импорта, который можно отменить.")
    record = history[-1]
    view = import_view(state)
    for path, existed, old, present, imported in reversed(record["changes"]):
        parent = view
        for key in path[:-1]:
            parent = parent.get(key)
            if not isinstance(parent, dict):
                break
        if not isinstance(parent, dict):
            continue
        key = path[-1]
        added_task = path[0] == "tasks" and len(path) == 2 and not existed
        if added_task or (key in parent) == present and parent.get(key) == imported:
            if existed:
                parent[key] = copy.deepcopy(old)
            else:
                parent.pop(key, None)
    def prune(mapping):
        for key in list(mapping):
            if isinstance(mapping[key], dict):
                prune(mapping[key])
                if not mapping[key]:
                    del mapping[key]
    for name in ["grades", "reported_grades", "sync"]:
        prune(view[name])
    state["tasks"] = list(view["tasks"].values())
    for task in state["tasks"]:
        choose_task_source(task)
    history.pop()
    return "Отменён импорт: " + record["label"]

def filter_deleted(state, incoming):
    result = []
    for task in incoming:
        blocked = False
        keys = set()
        for source in task["sources"]:
            if source_key(source) is not None:
                keys.add(source_key(source))
        for deleted in state.get("deleted_tasks", []):
            same_source = False
            for source in deleted["sources"]:
                if source_key(source) in keys:
                    same_source = True
            same_work = numbered_work_key(task) and numbered_work_key(task) == numbered_work_key(deleted)
            if same_source or make_deadline_key(task) == make_deadline_key(deleted) or (same_work and nearby_deadlines(task["deadline"], deleted["deadline"])):
                blocked = True
                break
        if not blocked:
            result.append(task)
    return result

def edit_deadline(state, task_id, values):
    allowed = {"title", "subject", "work", "deadline", "time", "description"}
    if set(values) - allowed or not all(isinstance(value, str) for value in values.values()):
        raise ValueError("Неверные поля задания.")
    if not values.get("title", "").strip():
        raise ValueError("Введите название задания.")
    date.fromisoformat(values["deadline"])
    if values.get("time") and not re.fullmatch(r"(?:[01]\d|2[0-3]):[0-5]\d", values["time"]):
        raise ValueError("Время укажите как ЧЧ:ММ или оставьте пустым.")
    for task in state["tasks"]:
        if task["id"] == task_id:
            task.setdefault("manual", {}).update(values)
            task.update(values)
            return
    raise ValueError("Задание не найдено.")

def delete_deadline(state, task_id):
    for position, task in enumerate(state["tasks"]):
        if task["id"] == task_id:
            state.setdefault("deleted_tasks", []).append(copy.deepcopy(task))
            del state["tasks"][position]
            return
    raise ValueError("Задание не найдено.")

def set_day_note(state, day, text):
    date.fromisoformat(day)
    if text.strip():
        state.setdefault("notes", {})[day] = text.strip()
    else:
        state.setdefault("notes", {}).pop(day, None)

def input_day(text):
    for pattern in ["%d.%m.%Y", "%Y-%m-%d"]:
        try:
            return datetime.strptime(text.strip(), pattern).date().isoformat()
        except ValueError:
            pass
    raise ValueError("Укажите дату как ДД.ММ.ГГГГ, например 01.10.2026.")

def clear_all(state):
    state.clear()
    state.update(new_state())

def repair_deadlines(state):
    original = state["tasks"]
    owners = {}
    corrected = 0
    candidates = []
    for task in original:
        if not task.get("manual"):
            kept = []
            for source in task["sources"]:
                if not any(marker in normalize_text(source["text"]) for marker in DISCUSSION_MARKERS):
                    kept.append(source)
            task["sources"] = kept
        if not task["sources"]:
            continue
        candidates.append(task)
        for source in task["sources"]:
            if source["kind"] == "telegram":
                message = {"id": source["message_id"], "chat": source["chat"], "date": source["date"],
                           "text": source["text"], "links": source["links"]}
                for parsed in create_deadlines(message, task["subject"], state["settings"]):
                    if parsed["sources"][0]["item"] == source["item"]:
                        if source["deadline"] != parsed["deadline"] or source["time"] != parsed["time"]:
                            source["deadline"], source["time"] = parsed["deadline"], parsed["time"]
                            corrected += 1
                        break
            choose_task_source(task)
            key = source_key(source)
            if key is not None:
                owners.setdefault(key, []).append(task)
    repaired, added, existing = merge_deadlines([], candidates)
    for task in repaired:
        for source in task["sources"]:
            for old in owners.get(source_key(source), []):
                if STATUSES.index(old["status"]) > STATUSES.index(task["status"]):
                    task["status"] = old["status"]
                for field in ["grade_subject", "grade_work"]:
                    if field in old:
                        task.setdefault(field, old[field])
                for field, value in old.get("manual", {}).items():
                    task.setdefault("manual", {}).setdefault(field, value)
        choose_task_source(task)
    state["tasks"] = repaired
    if len(repaired) < len(original) or corrected:
        state["repair_notice"] = "Объединено копий: %s, исключено обсуждений: %s, исправлено сроков: %s." % (
            len(candidates) - len(repaired), len(original) - len(candidates), corrected)

# ------------------------------ XLSX ------------------------------
XML_NS = {"s": "http://schemas.openxmlformats.org/spreadsheetml/2006/main"}
REL_ID = "{http://schemas.openxmlformats.org/officeDocument/2006/relationships}id"

def read_xlsx(raw):
    result = {}
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        names = set(archive.namelist())
        if "xl/workbook.xml" not in names:
            raise ValueError("Ответ не является XLSX. Возможно, Google требует вход в аккаунт.")
        if sum(info.file_size for info in archive.infolist()) > 80 * 1024 * 1024:
            raise ValueError("Слишком большая таблица (больше 80 МБ после распаковки).")
        strings = []
        if "xl/sharedStrings.xml" in names:
            for item in ET.fromstring(archive.read("xl/sharedStrings.xml")):
                strings.append("".join(node.text or "" for node in item.findall(".//s:t", XML_NS)))
        workbook = ET.fromstring(archive.read("xl/workbook.xml"))
        relations = {item.get("Id"): item.get("Target")
                     for item in ET.fromstring(archive.read("xl/_rels/workbook.xml.rels"))}
        for sheet in workbook.find("s:sheets", XML_NS):
            target = relations[sheet.get(REL_ID)]
            path = posixpath.normpath("xl/" + target)
            if target.startswith("/"):
                path = target.lstrip("/")
            if path not in names:
                continue
            root = ET.fromstring(archive.read(path))
            cells = {}
            for cell in root.findall("s:sheetData/s:row/s:c", XML_NS):
                text = cell.findtext("s:v", "", XML_NS)
                if cell.get("t") == "s" and text:
                    text = strings[int(text)]
                elif cell.get("t") == "inlineStr":
                    text = "".join(node.text or "" for node in cell.findall(".//s:t", XML_NS))
                if text:
                    cells[cell.get("r")] = text
            links = {}
            folder, filename = posixpath.split(path)
            relpath = folder + "/_rels/" + filename + ".rels"
            sheet_relations = {}
            if relpath in names:
                sheet_relations = {item.get("Id"): item.get("Target", "")
                                   for item in ET.fromstring(archive.read(relpath))}
            for link in root.findall("s:hyperlinks/s:hyperlink", XML_NS):
                url = sheet_relations.get(link.get(REL_ID), "")
                if url.startswith(("http://", "https://")):
                    links[link.get("ref")] = [url]
            result[sheet.get("name")] = {"cells": cells, "links": links}
    if not result:
        raise ValueError("В XLSX не найдено ни одного листа.")
    return result

def cell_position(address):
    match = re.fullmatch(r"([A-Z]+)(\d+)", address)
    if match is None:
        raise ValueError("Неверный адрес ячейки: " + address)
    return int(match.group(2)), match.group(1)

def extract_sheet_deadlines(workbook, settings, identity="schedule"):
    tasks = []
    warnings = []
    sheets = [name for name in workbook if "дедлайн" in normalize_text(name)]
    if not sheets:
        raise ValueError("В таблице не найден лист с названием «дедлайны».")
    for name in sheets:
        sheet = workbook[name]
        cells = sheet["cells"]
        context = None
        for address, text in sorted(cells.items(), key=lambda pair: cell_position(pair[0])):
            month = re.fullmatch(r"([а-я]+)\s+(\d{4})", normalize_text(text))
            if month:
                word = month.group(1).capitalize()
                if word in MONTH_NAMES:
                    context = date(int(month.group(2)), MONTH_NAMES.index(word) + 1, 1)
                continue
            if not is_deadline_message(text, settings):
                continue
            message_date = ""
            if context:
                message_date = context.isoformat()
            message = {"id": name + "!" + address, "chat": identity, "date": message_date, "text": text,
                       "links": find_links(text, sheet["links"].get(address, [])), "kind": "sheet"}
            found = create_deadlines(message, find_subject(text, settings), settings)
            if not found:
                warnings.append(name + "!" + address + ": не удалось распознать дату.")
            tasks.extend(found)
    if not tasks:
        raise ValueError("Лист дедлайнов пуст или его формат изменился. Сохранённые задачи оставлены.")
    return tasks, warnings

def parse_grade(value):
    text = str(value).strip().replace(",", ".")
    try:
        number = float(text)
    except ValueError:
        return None
    if not 0 <= number <= 10:
        return None
    return number

def extract_grades(workbook, student_name, settings):
    wanted = normalize_name(student_name)
    if len(wanted) < 2:
        raise ValueError("Укажите фамилию и имя, лучше полное ФИО.")
    grades = {}
    reported = {}
    warnings = []
    found_student = False
    for name, sheet in workbook.items():
        subject = find_subject(name, settings)
        if subject == "Не определён":
            continue
        rows = {}
        for address, text in sheet["cells"].items():
            row, column = cell_position(address)
            rows.setdefault(row, {})[column] = text
        headers = rows.get(1, {})
        name_columns = [column for column, title in headers.items() if "фио" in normalize_text(title)]
        if not name_columns:
            continue
        matches = []
        for row, values in rows.items():
            if row > 1 and any(normalize_name(values.get(column, "")) == wanted for column in name_columns):
                matches.append(row)
        if len(matches) > 1:
            raise ValueError(name + ": найдены несколько строк с одинаковым ФИО. Импорт отменён.")
        if not matches:
            warnings.append(name + ": ФИО не найдено, прежние оценки сохранены.")
            continue
        found_student = True
        row = matches[0]
        for column, header in headers.items():
            raw = rows[row].get(column, "")
            grade = parse_grade(raw)
            title = normalize_text(header)
            if "номера с ошибками" in title:
                continue
            if "итоговая оценка" in title or "накоп" in title:
                if grade is not None:
                    reported.setdefault(subject, {})[header.strip()] = grade
                continue
            work = infer_work(header)
            if not work:
                if "дз" in title and raw:
                    warnings.append(name + "!" + column + ": заголовок «" + header + "» без номера ДЗ, оценка не привязана.")
                continue
            if grade is not None:
                grades.setdefault(subject, {})[work] = {"value": grade, "cell": column + str(row), "sheet": name}
            elif raw.strip():
                warnings.append(name + "!" + column + str(row) + ": значение «" + raw + "» не распознано как оценка.")
    if not found_student:
        raise ValueError("Студент с указанным ФИО не найден на листах оценок. Прежние данные сохранены.")
    if not grades:
        raise ValueError("Для этого ФИО нет распознаваемых оценок. Пустые ячейки не заменяют сохранённые значения.")
    return grades, reported, warnings

def effective_grade(record):
    if record.get("manual") is not None:
        return record["manual"]
    return record.get("imported")

def complete_graded_tasks(state):
    person = " ".join(normalize_name(state["settings"]["student_name"]))
    grades = state["grades"].get(person, {})
    changed = False
    for task in state["tasks"]:
        subject = task.get("grade_subject", task["subject"])
        work = task.get("grade_work", task["work"])
        if effective_grade(grades.get(subject, {}).get(work, {})) is not None and task["status"] != "Готово":
            task["status"] = "Готово"
            changed = True
    return changed

def merge_grades(old, incoming, student_name):
    grades = copy.deepcopy(old)
    person = " ".join(normalize_name(student_name))
    student = grades.setdefault(person, {})
    changed = 0
    for subject, works in incoming.items():
        for work, record in works.items():
            stored = student.setdefault(subject, {}).setdefault(work, {"manual": None})
            if stored.get("imported") != record["value"]:
                changed += 1
            stored["imported"] = record["value"]
            stored["source"] = record["sheet"] + "!" + record["cell"]
            stored["updated"] = datetime.now(MSK).isoformat(timespec="seconds")
    return grades, changed

def set_manual_grade(state, subject, work, value):
    if value is not None and parse_grade(value) is None:
        raise ValueError("Оценка должна быть числом от 0 до 10.")
    person = " ".join(normalize_name(state["settings"]["student_name"]))
    record = state["grades"].setdefault(person, {}).setdefault(subject, {}).setdefault(work, {})
    record["manual"] = value
    complete_graded_tasks(state)

def set_task_grade(state, task_id, subject, work, value):
    set_manual_grade(state, subject, work, value)
    for task in state["tasks"]:
        if task["id"] == task_id:
            task["grade_subject"] = subject
            task["grade_work"] = work
            break
    complete_graded_tasks(state)

def grade_summary(state, subject):
    person = " ".join(normalize_name(state["settings"]["student_name"]))
    records = state["grades"].get(person, {}).get(subject, {})
    if subject == MENTOR:
        passed = sum(1 for work, record in records.items() if work.startswith("ДЗ ") and
                     effective_grade(record) is not None and effective_grade(record) >= 4)
        return "Зачёт по ДЗ: выполнено " + str(passed) + "/3 необходимых (из 4)."
    weights = state["settings"]["weights"].get(subject, {})
    contribution = known_weight = 0
    count = 0
    for work, weight in weights.items():
        value = effective_grade(records.get(work, {}))
        if value is not None:
            contribution += value * weight
            known_weight += weight
            count += 1
    total_weight = sum(weights.values())
    text = "Набрано по известным оценкам: %.4f, заполнено %s/%s работ, учтён вес %.4g из %.4g." % (
        contribution, count, len(weights), known_weight, total_weight)
    text += " Возможный диапазон по формуле: %.4f–%.4f." % (contribution, contribution + 10 * (total_weight - known_weight))
    if abs(total_weight - 1) > .00001:
        text += " Внимание: сумма весов %.4g, уточните формулу. Веса не нормализованы автоматически." % total_weight
    return text


# -------------------------- Синхронизация --------------------------
def spreadsheet_id(value):
    match = re.search(r"/spreadsheets/d/([A-Za-z0-9_-]+)", value)
    identifier = value.strip()
    if match:
        identifier = match.group(1)
    if not re.fullmatch(r"[A-Za-z0-9_-]{15,}", identifier):
        raise ValueError("Укажите ссылку Google Sheets или ID таблицы.")
    return identifier

def download_spreadsheet(identifier):
    url = "https://docs.google.com/spreadsheets/d/" + identifier + "/export?format=xlsx"
    request = urllib.request.Request(url, headers={"User-Agent": "StudyFlow/1.0"})
    with urllib.request.urlopen(request, timeout=8) as response:
        raw = response.read(12 * 1024 * 1024 + 1)
    if len(raw) > 12 * 1024 * 1024:
        raise ValueError("Таблица больше 12 МБ. Импортируйте локальную копию.")
    if not raw.startswith(b"PK"):
        raise ValueError("Google не вернул XLSX. Нужен доступ без входа или локальный импорт файла.")
    return raw

def _import_spreadsheet(state, raw, kind, identity="local", synced=False):
    workbook = read_xlsx(raw)
    settings = state["settings"]
    changes = {}
    if kind == "deadlines":
        incoming, warning = extract_sheet_deadlines(workbook, settings, identity)
        incoming = filter_deleted(state, incoming)
        previous = {source_key(s) for task in state["tasks"] for s in task["sources"]
                    if s["kind"] == "sheet" and s["chat"] == identity}
        current = {source_key(s) for task in incoming for s in task["sources"]}
        missing = previous - current
        if missing:
            warning.append("Из таблицы исчезли %s прежних записей, они сохранены в приложении." % len(missing))
        # Дата сообщения нужна для контекста года. После извлечения используем
        # момент импорта для выбора самой свежей версии источника.
        now = datetime.now(MSK).isoformat(timespec="seconds")
        for task in incoming:
            task["sources"][0]["date"] = now
        changes["tasks"], added, existing = merge_deadlines(state["tasks"], incoming)
        summary = "Дедлайны: добавлено %s, уже существовало %s." % (added, existing)
    else:
        incoming, reported, warning = extract_grades(workbook, settings["student_name"], settings)
        person = " ".join(normalize_name(settings["student_name"]))
        old = state["grades"].get(person, {})
        missing = [(subject, work) for subject, works in old.items() for work, record in works.items()
                   if record.get("imported") is not None and work not in incoming.get(subject, {})]
        if missing:
            warning.append("В источнике отсутствуют %s прежних оценок, они сохранены." % len(missing))
        changes["grades"], changed = merge_grades(state["grades"], incoming, settings["student_name"])
        changes["reported_grades"] = copy.deepcopy(state["reported_grades"])
        for subject, values in reported.items():
            changes["reported_grades"].setdefault(person, {}).setdefault(subject, {}).update(values)
        summary = "Оценки: прочитано %s, новых или изменённых %s." % (sum(len(w) for w in incoming.values()), changed)
    # Обновляем только после полного разбора, ошибка не меняет прежние данные.
    state.update(changes)
    if synced:
        state["sync"][kind] = {"last_success": datetime.now(MSK).isoformat(timespec="seconds"),
                               "error": "", "warnings": warning}
    return summary, warning

def import_spreadsheet(state, raw, kind, identity="local", synced=False, label=None):
    label = label or SOURCE_LABELS.get(kind, "Таблица") + ": " + identity
    return record_import(state, label, lambda: _import_spreadsheet(state, raw, kind, identity, synced))

def apply_sync_results(state, results):
    output = []
    for kind, raw, error, identity in results:
        label = SOURCE_LABELS.get(kind, "Оценки")
        try:
            if error:
                raise ValueError(error)
            summary, warnings = import_spreadsheet(state, raw, kind, identity, synced=True)
            output.append("\n".join([summary] + warnings))
        except (ValueError, KeyError, TypeError, AttributeError, ET.ParseError, zipfile.BadZipFile, IndexError) as problem:
            state["sync"].setdefault(kind, {})["error"] = str(problem)
            output.append(label + ": синхронизация не прошла, сохранённые данные доступны. " + str(problem))
    return output

def _import_telegram_data(state, paths):
    messages, files, errors = read_telegram_export(paths, state["settings"])
    if not files:
        raise ValueError("Не прочитан ни один файл экспорта. " + "\n".join(errors))
    tasks, unresolved = extract_deadlines(messages, state["settings"])
    tasks = filter_deleted(state, tasks)
    state["tasks"], added, existing = merge_deadlines(state["tasks"], tasks)
    summary = "Файлов: %s, сообщений: %s, найдено задач: %s, добавлено: %s, уже было: %s." % (
        files, sum(not m["service"] for m in messages), len(tasks), added, existing)
    return "\n".join([summary] + errors + unresolved)

def import_telegram_data(state, paths):
    label = "Telegram: " + ", ".join(str(Path(path).name) for path in paths)
    return record_import(state, label, lambda: _import_telegram_data(state, paths))

def import_local_spreadsheet(state, path, kind):
    identity = "local"
    if kind == "deadlines":
        identity = "local_schedule"
        if state["settings"]["deadlines_sheet"].strip():
            identity = spreadsheet_id(state["settings"]["deadlines_sheet"])
    summary, warnings = import_spreadsheet(state, Path(path).read_bytes(), kind, identity, label=SOURCE_LABELS[kind] + ": " + Path(path).name)
    return "\n".join([summary] + warnings)

def sync_sources(settings):
    results = []
    for kind, key in [("deadlines", "deadlines_sheet"), ("grades", "grades_sheet")]:
        try:
            identifier = spreadsheet_id(settings[key])
            results.append((kind, download_spreadsheet(identifier), "", identifier))
        except (OSError, ValueError) as error:
            results.append((kind, None, str(error), settings[key]))
    return results


# ---------------------------- iCalendar ----------------------------
def ics_escape(text):
    return str(text).replace("\\", "\\\\").replace("\r", "").replace("\n", "\\n").replace(";", "\\;").replace(",", "\\,")

def fold_ics_line(line):
    # RFC 5545: не больше 75 байтов в строке, не разрываем UTF-8-символ.
    pieces = []
    current = ""
    for character in line:
        if len((current + character).encode("utf-8")) > 75:
            pieces.append(current)
            current = " "
        current += character
    pieces.append(current)
    return "\r\n".join(pieces)

def export_ics(tasks, path):
    lines = ["BEGIN:VCALENDAR", "VERSION:2.0", "PRODID:-//StudyFlow//RU", "CALSCALE:GREGORIAN"]
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    for task in tasks:
        if task["status"] == "Готово":
            continue
        lines.extend(["BEGIN:VEVENT", "UID:" + task["id"] + "@studyflow.local", "DTSTAMP:" + stamp])
        day = date.fromisoformat(task["deadline"])
        if task["time"]:
            hour, minute = map(int, task["time"].split(":"))
            start = datetime(day.year, day.month, day.day, hour, minute, tzinfo=MSK).astimezone(timezone.utc)
            lines.extend(["DTSTART:" + start.strftime("%Y%m%dT%H%M%SZ"),
                          "DTEND:" + (start + timedelta(minutes=1)).strftime("%Y%m%dT%H%M%SZ")])
        else:
            lines.extend(["DTSTART;VALUE=DATE:" + day.strftime("%Y%m%d"),
                          "DTEND;VALUE=DATE:" + (day + timedelta(days=1)).strftime("%Y%m%d")])
        lines.append("SUMMARY:" + ics_escape(task["subject"] + ": " + task["title"]))
        description = "Статус: " + task["status"] + "\n" + "\n".join(task["links"])
        lines.extend(["DESCRIPTION:" + ics_escape(description), "END:VEVENT"])
    lines.append("END:VCALENDAR")
    Path(path).write_bytes(("\r\n".join(fold_ics_line(line) for line in lines) + "\r\n").encode("utf-8"))


# ---------------------------- Интерфейс ----------------------------
def keyboard_command(keysym, keycode, windows=False):
    key = keysym.lower()
    if windows and keycode in [65, 67, 86, 88]:
        key = chr(keycode).lower()
    commands = {"v": "paste", "м": "paste", "cyrillic_em": "paste", "c": "copy", "с": "copy",
                "cyrillic_es": "copy", "x": "cut", "ч": "cut", "cyrillic_che": "cut",
                "a": "all", "ф": "all", "cyrillic_ef": "all"}
    return commands.get(key)

def launch_gui(state, data_path=DATA_FILE, skip_sync=False):
    import tkinter as tk
    from tkinter import filedialog, messagebox, ttk

    def edit_action(widget, command):
        if command == "all":
            if widget.winfo_class() == "Text":
                widget.tag_add("sel", "1.0", "end-1c")
            else:
                widget.selection_range(0, "end")
        else:
            widget.event_generate({"paste": "<<Paste>>", "copy": "<<Copy>>", "cut": "<<Cut>>"}[command])

    def edit_menu(widget):
        menu = tk.Menu(widget, tearoff=0)
        for label, command in [("Вырезать", "cut"), ("Копировать", "copy"), ("Вставить", "paste"), ("Выделить всё", "all")]:
            menu.add_command(label=label, command=lambda action=command: edit_action(widget, action))
        def shortcut(event):
            command = keyboard_command(event.keysym, event.keycode, os.name == "nt")
            if command:
                edit_action(widget, command)
                return "break"
        def popup(event):
            try:
                menu.tk_popup(event.x_root, event.y_root)
            finally:
                menu.grab_release()
        widget.bind("<Control-KeyPress>", shortcut)
        widget.bind("<Button-3>", popup)
        return widget

    def frame(parent, **packing):
        widget = ttk.Frame(parent, padding=8)
        widget.pack(**packing)
        return widget

    def buttons(parent, actions):
        for title, command in actions:
            ttk.Button(parent, text=title, command=command).pack(side="left", padx=3)

    def table(parent, columns, height):
        widget = ttk.Treeview(parent, columns=list(range(len(columns))), show="headings", height=height)
        for index, (title, width) in enumerate(columns):
            widget.heading(index, text=title)
            widget.column(index, width=width, minwidth=50)
        widget.pack(fill="both", expand=True, pady=5)
        return widget

    def field(parent, label, value="", choices=None):
        ttk.Label(parent, text=label).pack(anchor="w")
        if choices is None:
            widget = ttk.Entry(parent, width=60)
            widget.insert(0, value)
        else:
            widget = ttk.Combobox(parent, values=choices, state="readonly", width=45)
            widget.set(value)
        widget.pack(fill="x", pady=(2, 8))
        return edit_menu(widget)

    def show_text(widget, text):
        widget.configure(state="normal")
        widget.delete("1.0", "end")
        widget.insert("1.0", text)
        widget.configure(state="disabled")

    def dialog(parent, title):
        window = tk.Toplevel(parent)
        window.title(title)
        window.transient(parent)
        return window, frame(window, fill="both", expand=True)

    class StudyFlowApp:
        def __init__(self, root):
            self.root, self.state = root, state
            self.selected_date = datetime.now(MSK).date()
            self.month = self.selected_date.replace(day=1)
            self.busy = False
            self.notes_text = None
            self.result_queue = queue.Queue()
            root.title("StudyFlow — дедлайны и оценки")
            root.geometry("1160x810")
            root.minsize(960, 700)
            style = ttk.Style()
            style.theme_use("clam")
            style.configure("Treeview", rowheight=27)
            toolbar = frame(root, fill="x")
            buttons(toolbar, [
                ("Импорт Telegram", lambda: self.import_data("telegram")),
                ("Импорт папки", lambda: self.import_data("folder")),
                ("Синхронизировать", self.start_sync), ("Экспорт .ics", self.save_ics),
                ("ФИО и источники", self.profile), ("Правила", self.rules)])
            data_toolbar = frame(root, fill="x")
            buttons(data_toolbar, [("Заметки", self.notes_list), ("Очистить всё", lambda: self.manage_data("clear"))])
            self.undo_button = ttk.Button(data_toolbar, text="Отменить последний импорт", command=lambda: self.manage_data("undo"))
            self.undo_button.pack(side="left", padx=3)
            self.notice = tk.StringVar(value="Сохранённые данные загружены. " + state.get("repair_notice", ""))
            ttk.Label(root, textvariable=self.notice, wraplength=1090).pack(fill="x", padx=12)
            tabs = ttk.Notebook(root)
            tabs.pack(fill="both", expand=True, padx=12, pady=8)
            calendar_tab, grades_tab = ttk.Frame(tabs), ttk.Frame(tabs)
            tabs.add(calendar_tab, text="Календарь")
            tabs.add(grades_tab, text="Оценки")
            left = frame(calendar_tab, side="left", fill="y")
            navigation = frame(left, fill="x")
            ttk.Button(navigation, text="‹", width=3, command=lambda: self.change_month(-1)).pack(side="left")
            self.month_label = ttk.Label(navigation, width=21, anchor="center")
            self.month_label.pack(side="left")
            ttk.Button(navigation, text="›", width=3, command=lambda: self.change_month(1)).pack(side="left")
            ttk.Button(left, text="Сегодня", command=lambda: self.select_day(datetime.now(MSK).date())).pack(fill="x")
            self.calendar_grid = frame(left)
            ttk.Label(left, text="В скобках указано число задач.").pack(anchor="w")
            ttk.Label(left, text="Просроченные и ближайшие 14 дней").pack(anchor="w", pady=8)
            self.upcoming = tk.Listbox(left, width=38, height=12)
            self.upcoming.pack(fill="both", expand=True)
            self.upcoming.bind("<<ListboxSelect>>", self.select_upcoming)
            right = frame(calendar_tab, side="left", fill="both", expand=True)
            self.day_label = ttk.Label(right)
            self.day_label.pack(anchor="w")
            self.task_table = table(right, [("Предмет", 190), ("Задание", 160), ("Время", 65),
                                            ("Статус", 95), ("Оценка", 65)], 8)
            self.task_table.bind("<<TreeviewSelect>>", self.show_task)
            controls = frame(right, fill="x")
            self.status_box = ttk.Combobox(controls, values=STATUSES, state="readonly", width=16)
            self.status_box.pack(side="left")
            self.status_box.bind("<<ComboboxSelected>>", self.change_status)
            buttons(controls, [("Добавить / изменить оценку", self.task_grade)])
            task_controls = frame(right, fill="x")
            buttons(task_controls, [("Редактировать", self.task_editor), ("Удалить", self.remove_task),
                                    ("Заметка на день", self.note_dialog)])
            ttk.Label(right, text="Источники выбранной задачи").pack(anchor="w")
            source_frame = frame(right, fill="both", expand=True)
            self.source_text = edit_menu(tk.Text(source_frame, wrap="word", height=10))
            self.source_text.pack(side="left", fill="both", expand=True)
            scrollbar = ttk.Scrollbar(source_frame, command=self.source_text.yview)
            scrollbar.pack(side="right", fill="y")
            self.source_text.configure(yscrollcommand=scrollbar.set)
            self.links_box = tk.Listbox(right, height=3)
            self.links_box.pack(fill="x")
            self.links_box.bind("<Double-1>", self.open_link)
            ttk.Button(right, text="Открыть ссылку", command=self.open_link).pack(anchor="w")
            grade_toolbar = frame(grades_tab, fill="x")
            buttons(grade_toolbar, [
                ("Импорт ведомости XLSX", lambda: self.import_data("grades")),
                ("Импорт дедлайнов XLSX", lambda: self.import_data("deadlines")),
                ("Добавить / изменить оценку", self.grade_dialog)])
            self.grade_table = table(grades_tab, [("Предмет", 320), ("Работа", 145),
                                                  ("В расчёте", 100), ("Из ведомости", 120), ("Вручную", 100)], 12)
            self.grade_table.bind("<Double-1>", self.edit_selected_grade)
            self.summary = tk.Text(grades_tab, height=10, wrap="word")
            self.summary.pack(fill="x", padx=8, pady=8)
            self.refresh()
            if self.state["settings"]["sync_on_start"] and not skip_sync:
                root.after(300, self.start_sync)

        def update(self, action, window=None):
            selected = self.task_table.selection()
            candidate = copy.deepcopy(self.state)
            try:
                result = action(candidate)
                complete_graded_tasks(candidate)
                save_data(candidate, data_path)
            except (OSError, ValueError, KeyError, TypeError, AttributeError, ET.ParseError, zipfile.BadZipFile, IndexError) as error:
                messagebox.showerror("Не удалось выполнить", str(error), parent=self.root)
                return False
            self.state = candidate
            if window is not None:
                window.destroy()
            self.refresh()
            if selected and selected[0] in self.task_positions:
                task = self.state["tasks"][self.task_positions[selected[0]]]
                if task["deadline"] == self.selected_date.isoformat():
                    self.task_table.selection_set(selected[0])
                    self.show_task()
            if result:
                messagebox.showinfo("Готово", result, parent=self.root)
            return True

        def refresh(self):
            self.reference_date = datetime.now(MSK).date()
            self.tasks_by_day = {}
            self.task_positions = {}
            for position, task in enumerate(self.state["tasks"]):
                self.tasks_by_day.setdefault(task["deadline"], []).append(task)
                self.task_positions[task["id"]] = position
            self.show_month()
            limit = (self.reference_date + timedelta(days=14)).isoformat()
            self.nearest = sorted([t for t in self.state["tasks"] if t["status"] != "Готово" and t["deadline"] <= limit],
                                  key=lambda t: (t["deadline"], t["time"], t["subject"]))
            self.upcoming.delete(0, "end")
            for task in self.nearest:
                self.upcoming.insert("end", task["deadline"][5:] + " · " + task["title"] + " · " + task["subject"])
            self.fill_grades()
            if getattr(self, "undo_button", None) is not None:
                button_state = "disabled"
                if self.state.get("imports"):
                    button_state = "normal"
                self.undo_button.configure(state=button_state)
            self.fill_notes()

        def show_month(self):
            self.month_label.configure(text=MONTH_NAMES[self.month.month - 1] + " " + str(self.month.year))
            for widget in self.calendar_grid.winfo_children():
                widget.destroy()
            for column, title in enumerate(["Пн", "Вт", "Ср", "Чт", "Пт", "Сб", "Вс"]):
                ttk.Label(self.calendar_grid, text=title, anchor="center", width=4).grid(row=0, column=column)
            for row, week in enumerate(calendar.monthcalendar(self.month.year, self.month.month), 1):
                for column, day in enumerate(week):
                    if not day:
                        continue
                    current = date(self.month.year, self.month.month, day)
                    count = len(self.tasks_by_day.get(current.isoformat(), []))
                    label, color = str(day), "white"
                    if count:
                        label += "\n(" + str(count) + ")"
                        color, selected_color = "#FF9B95", "#FC7F73"
                        if all(task["status"] == "Готово" for task in self.tasks_by_day[current.isoformat()]):
                            color, selected_color = "#52CEB9", "#00BCA9"
                        if current == self.selected_date:
                            color = selected_color
                    if current.isoformat() in self.state.get("notes", {}):
                        label += " ✎"
                    tk.Button(self.calendar_grid, text=label, width=4, height=2, bg=color,
                              activebackground=color,
                              command=lambda d=current: self.select_day(d)).grid(row=row, column=column, padx=2, pady=2)
            self.fill_day()

        def select_day(self, day):
            self.selected_date, self.month = day, day.replace(day=1)
            if self.reference_date != datetime.now(MSK).date():
                self.refresh()
            else:
                self.show_month()

        def select_upcoming(self, event=None):
            selected = self.upcoming.curselection()
            if selected:
                task = self.nearest[selected[0]]
                self.select_day(date.fromisoformat(task["deadline"]))
                self.task_table.selection_set(task["id"])
                self.task_table.see(task["id"])
                self.show_task()

        def change_month(self, delta):
            number = self.month.year * 12 + self.month.month - 1 + delta
            self.select_day(date(number // 12, number % 12 + 1, 1))

        def selected_task(self):
            selected = self.task_table.selection()
            if selected:
                return self.state["tasks"][self.task_positions[selected[0]]]

        def fill_day(self):
            self.day_label.configure(text=self.selected_date.strftime("%d.%m.%Y"))
            self.task_table.delete(*self.task_table.get_children())
            person = " ".join(normalize_name(self.state["settings"]["student_name"]))
            grades = self.state["grades"].get(person, {})
            tasks = self.tasks_by_day.get(self.selected_date.isoformat(), [])
            for task in sorted(tasks, key=lambda t: (t["time"], t["subject"])):
                record = grades.get(task.get("grade_subject", task["subject"]), {}).get(task.get("grade_work", task["work"]), {})
                values = [task["subject"], task["title"], task["time"] or "—", task["status"], effective_grade(record)]
                self.task_table.insert("", "end", iid=task["id"], values=display_values(values))
            self.status_box.set("")
            show_text(self.source_text, "Выберите задачу. Время «—» значит, что оно не указано в источнике.")
            self.links_box.delete(0, "end")

        def show_task(self, event=None):
            task = self.selected_task()
            if task:
                self.status_box.set(task["status"])
                parts = ["Задание: %s, %s\nСрок: %s %s" % (task["subject"], task["title"], task["deadline"], task["time"])]
                if task.get("description"):
                    parts.append("Моё описание:\n" + task["description"])
                for source in task["sources"]:
                    parts.append("Исходное сообщение: %s · %s · %s\n%s" % (source["kind"], source["message_id"], source["date"], source["text"]))
                    for version in source.get("history", []):
                        parts.append("Предыдущий текст источника:\n" + version["text"])
                show_text(self.source_text, "\n\n".join(parts))
                self.links_box.delete(0, "end")
                for link in task["links"]:
                    self.links_box.insert("end", link)

        def change_status(self, event=None):
            task = self.selected_task()
            if task:
                status = self.status_box.get()
                def change(candidate):
                    candidate["tasks"][self.task_positions[task["id"]]]["status"] = status
                self.update(change)

        def open_link(self, event=None):
            selected = self.links_box.curselection()
            if selected:
                webbrowser.open(self.links_box.get(selected[0]))

        def task_editor(self):
            task = self.selected_task()
            if not task:
                return
            window, body = dialog(self.root, "Редактирование дедлайна")
            entries = {}
            values = dict(task, deadline=date.fromisoformat(task["deadline"]).strftime("%d.%m.%Y"))
            for key, label in [("title", "Название"), ("subject", "Предмет"), ("work", "Работа для оценки, например ДЗ 1"),
                               ("deadline", "Дата, ДД.ММ.ГГГГ"), ("time", "Время, ЧЧ:ММ, можно оставить пустым")]:
                entries[key] = field(body, label, values[key])
            ttk.Label(body, text="Моё описание, исходные сообщения останутся отдельно").pack(anchor="w")
            description = edit_menu(tk.Text(body, height=5, wrap="word"))
            description.pack(fill="both", expand=True)
            description.insert("1.0", task.get("description", ""))
            def change(candidate):
                edited = {}
                for key, widget in entries.items():
                    edited[key] = widget.get().strip()
                edited["deadline"] = input_day(edited["deadline"])
                edited["description"] = description.get("1.0", "end-1c").strip()
                edit_deadline(candidate, task["id"], edited)
            def save():
                day = input_day(entries["deadline"].get())
                if self.update(change, window):
                    self.select_day(date.fromisoformat(day))
                    self.task_table.selection_set(task["id"])
                    self.show_task()
            def save_checked():
                try:
                    save()
                except ValueError as error:
                    messagebox.showerror("Неверная дата", str(error), parent=window)
            ttk.Label(body, text="Ручные правки сохранятся при новом импорте.").pack(pady=6)
            ttk.Button(body, text="Сохранить", command=save_checked).pack(fill="x")

        def remove_task(self):
            task = self.selected_task()
            if task and messagebox.askyesno("Удалить дедлайн", "Удалить «%s»?\nПовторный импорт не вернёт это задание." % task["title"], parent=self.root):
                self.update(lambda candidate: delete_deadline(candidate, task["id"]))

        def manage_data(self, operation):
            if self.busy:
                messagebox.showinfo("Синхронизация", "Сначала дождитесь конца синхронизации.", parent=self.root)
                return
            if operation == "undo":
                if not self.state.get("imports"):
                    return
                title = "Отменить последний импорт"
                text = "Отменить «%s»?\nНовые записи этого импорта исчезнут, прежние данные восстановятся. Заметки по дням сохранятся." % self.state["imports"][-1]["label"]
                action = undo_import
            else:
                title = "Очистить всё"
                text = "Удалить все дедлайны, оценки, заметки, историю импортов и настройки?"
                action = clear_all
            def change(candidate):
                if self.busy:
                    raise ValueError("Сначала дождитесь конца синхронизации.")
                return action(candidate)
            if messagebox.askyesno(title, text, parent=self.root) and self.update(change):
                self.notice.set(title + ", готово.")
                if operation == "clear":
                    for child in self.root.winfo_children():
                        if isinstance(child, tk.Toplevel):
                            child.destroy()
                    self.notes_text = None

        def fill_notes(self):
            widget = getattr(self, "notes_text", None)
            if widget is None or not widget.winfo_exists():
                return
            parts = []
            for day, text in sorted(self.state.get("notes", {}).items(), reverse=True):
                parts.append(date.fromisoformat(day).strftime("%d.%m.%Y") + "\n" + text)
            show_text(widget, "\n\n".join(parts) or "Заметок пока нет.")

        def notes_list(self):
            if self.notes_text is not None and self.notes_text.winfo_exists():
                self.notes_text.winfo_toplevel().lift()
                return
            window, body = dialog(self.root, "Все заметки")
            window.geometry("700x600")
            date_box = field(body, "Дата для изменения заметки, ДД.ММ.ГГГГ", self.selected_date.strftime("%d.%m.%Y"))
            ttk.Button(body, text="Открыть заметку на эту дату", command=lambda: self.note_dialog(date_box.get())).pack(fill="x")
            area = frame(body, fill="both", expand=True)
            self.notes_text = edit_menu(tk.Text(area, wrap="word"))
            self.notes_text.pack(side="left", fill="both", expand=True)
            scrollbar = ttk.Scrollbar(area, command=self.notes_text.yview)
            scrollbar.pack(side="right", fill="y")
            self.notes_text.configure(yscrollcommand=scrollbar.set)
            self.fill_notes()

        def note_dialog(self, day=None):
            if day is None:
                day = self.selected_date.isoformat()
            try:
                day = input_day(day)
            except ValueError as error:
                messagebox.showerror("Неверная дата", str(error), parent=self.root)
                return
            window, body = dialog(self.root, "Заметка на " + date.fromisoformat(day).strftime("%d.%m.%Y"))
            ttk.Label(body, text="Пустой текст удаляет заметку.").pack(anchor="w")
            editor = edit_menu(tk.Text(body, width=65, height=12, wrap="word"))
            editor.pack(fill="both", expand=True)
            editor.insert("1.0", self.state.get("notes", {}).get(day, ""))
            ttk.Button(body, text="Сохранить", command=lambda: self.update(
                lambda candidate: set_day_note(candidate, day, editor.get("1.0", "end-1c")), window)).pack(fill="x")

        def import_data(self, kind):
            if kind == "folder":
                path = filedialog.askdirectory(parent=self.root, title="Папка экспорта Telegram")
                paths = [path]
            elif kind == "telegram":
                paths = filedialog.askopenfilenames(parent=self.root, filetypes=[("Telegram", "*.zip *.html *.json")])
            else:
                path = filedialog.askopenfilename(parent=self.root, filetypes=[("Excel", "*.xlsx")])
                paths = [path]
            if not paths or not paths[0]:
                return
            if kind in ["folder", "telegram"]:
                self.update(lambda candidate: import_telegram_data(candidate, paths))
            else:
                self.update(lambda candidate: import_local_spreadsheet(candidate, paths[0], kind))

        def save_ics(self):
            path = filedialog.asksaveasfilename(parent=self.root, defaultextension=".ics", initialfile="studyflow_deadlines.ics")
            if path:
                try:
                    export_ics(self.state["tasks"], path)
                    messagebox.showinfo("Готово", "Незавершённые задачи сохранены в ICS. Время московское.", parent=self.root)
                except OSError as error:
                    messagebox.showerror("Ошибка экспорта", str(error), parent=self.root)

        def fill_grades(self):
            self.grade_table.delete(*self.grade_table.get_children())
            person = " ".join(normalize_name(self.state["settings"]["student_name"]))
            records = self.state["grades"].get(person, {})
            text = ["Студент: " + self.state["settings"]["student_name"],
                    "Ручная оценка важнее импортированной. Пустая ячейка не равна нулю."]
            for subject, works in self.state["settings"]["weights"].items():
                for work in works:
                    record = records.get(subject, {}).get(work, {})
                    self.grade_table.insert("", "end", values=display_values(
                        [subject, work, effective_grade(record), record.get("imported"), record.get("manual")]))
                text.extend(["", subject, grade_summary(self.state, subject)])
                reported = self.state["reported_grades"].get(person, {}).get(subject)
                if reported:
                    text.append("Итоги из ведомости, отдельно от расчёта: " + str(reported))
            show_text(self.summary, "\n".join(text))

        def task_grade(self):
            task = self.selected_task()
            if task:
                self.grade_dialog(task.get("grade_subject", task["subject"]), task.get("grade_work", task["work"]), task["id"])

        def edit_selected_grade(self, event=None):
            selected = self.grade_table.selection()
            if selected:
                values = self.grade_table.item(selected[0], "values")
                self.grade_dialog(values[0], values[1])

        def grade_dialog(self, subject="", work="", task_id=None):
            window, body = dialog(self.root, "Оценка")
            settings = self.state["settings"]
            subjects = list(settings["weights"])
            if not subjects:
                messagebox.showinfo("Правила", "Сначала добавьте предметы и работы в weights.", parent=window)
                window.destroy()
                return
            if subject not in subjects:
                subject = subjects[0]
            subject_box = field(body, "Предмет", subject, subjects)
            work_box = field(body, "Работа", work, [])
            grade_box = field(body, "Оценка 0–10, пустое поле убирает ручную оценку")
            def update_works(event=None):
                works = list(settings["weights"][subject_box.get()])
                work_box.configure(values=works)
                if work_box.get() not in works:
                    work_box.set(works[0])
                person = " ".join(normalize_name(settings["student_name"]))
                record = self.state["grades"].get(person, {}).get(subject_box.get(), {}).get(work_box.get(), {})
                grade_box.delete(0, "end")
                value = effective_grade(record)
                if value is not None:
                    grade_box.insert(0, str(value))
            def change(candidate):
                text = grade_box.get().strip()
                value = parse_grade(text)
                if text and value is None:
                    raise ValueError("Введите число от 0 до 10.")
                if task_id:
                    set_task_grade(candidate, task_id, subject_box.get(), work_box.get(), value)
                else:
                    set_manual_grade(candidate, subject_box.get(), work_box.get(), value)
            subject_box.bind("<<ComboboxSelected>>", update_works)
            work_box.bind("<<ComboboxSelected>>", update_works)
            update_works()
            ttk.Button(body, text="Сохранить", command=lambda: self.update(change, window)).pack(fill="x")

        def profile(self):
            if self.busy:
                messagebox.showinfo("Синхронизация", "Сначала дождитесь конца синхронизации.", parent=self.root)
                return
            window, body = dialog(self.root, "ФИО и источники")
            entries = {}
            for key, label in [("student_name", "Полное ФИО"), ("grades_sheet", "Ссылка или ID ведомости"),
                               ("deadlines_sheet", "Ссылка или ID таблицы дедлайнов"), ("chat_key", "Название чата Telegram")]:
                entries[key] = field(body, label, self.state["settings"][key])
            automatic = tk.BooleanVar(value=self.state["settings"]["sync_on_start"])
            ttk.Checkbutton(body, text="Синхронизировать при запуске", variable=automatic).pack(anchor="w")
            ttk.Label(body, text="Закрытые таблицы можно импортировать файлом XLSX.").pack(pady=8)
            def change(candidate):
                if self.busy:
                    raise ValueError("Сначала дождитесь конца синхронизации.")
                settings = candidate["settings"]
                settings.update({key: widget.get().strip() for key, widget in entries.items()})
                settings["sync_on_start"] = automatic.get()
                for key in ["grades_sheet", "deadlines_sheet"]:
                    if settings[key]:
                        spreadsheet_id(settings[key])
                if automatic.get() and not (settings["grades_sheet"] or settings["deadlines_sheet"]):
                    raise ValueError("Для синхронизации укажите хотя бы одну таблицу.")
                if settings["student_name"] and len(normalize_name(settings["student_name"])) < 2:
                    raise ValueError("Укажите фамилию и имя.")
            ttk.Button(body, text="Сохранить", command=lambda: self.update(change, window)).pack(fill="x")

        def rules(self):
            window, body = dialog(self.root, "Правила")
            window.geometry("850x660")
            ttk.Label(body, text="Измените JSON и сохраните. Подсказки в RULES_GUIDE.md.\nПравила применятся при следующем импорте.").pack()
            editor = edit_menu(tk.Text(body, wrap="none"))
            editor.pack(fill="both", expand=True)
            keys = ["subject_aliases", "task_markers", "deadline_markers", "exclude_markers", "weights"]
            editor.insert("1.0", json.dumps({key: self.state["settings"][key] for key in keys}, ensure_ascii=False, indent=2))
            def change(candidate):
                parsed = json.loads(editor.get("1.0", "end"))
                if not isinstance(parsed, dict) or set(parsed) != set(keys):
                    raise ValueError("Оставьте все пять разделов правил.")
                candidate["settings"].update(parsed)
                validate_settings(candidate["settings"])
            ttk.Button(body, text="Сохранить", command=lambda: self.update(change, window)).pack(pady=8)

        def start_sync(self):
            if not self.busy:
                self.busy = True
                settings = copy.deepcopy(self.state["settings"])
                self.notice.set("Синхронизация таблиц…")
                threading.Thread(target=lambda: self.result_queue.put(sync_sources(settings)), daemon=True).start()
                self.root.after(100, self.finish_sync)

        def finish_sync(self):
            try:
                results = self.result_queue.get_nowait()
            except queue.Empty:
                self.root.after(100, self.finish_sync)
                return
            self.busy = False
            if self.update(lambda candidate: "\n\n".join(apply_sync_results(candidate, results))):
                text = []
                for kind, record in self.state["sync"].items():
                    label = SOURCE_LABELS.get(kind, "Оценки")
                    text.append(label + ", последний успех: " + record.get("last_success", "ещё не было"))
                    if record.get("error"):
                        text.append("Синхронизация не прошла, сохранённые данные доступны.")
                    if record.get("warnings"):
                        text.append("Есть предупреждения, подробности в окне результата.")
                self.notice.set(" ".join(text))

    def display_values(values):
        result = []
        for value in values:
            if value is None:
                value = "—"
            result.append(value)
        return result

    root = tk.Tk()
    StudyFlowApp(root)
    root.mainloop()

def main():
    import argparse
    parser = argparse.ArgumentParser(description="StudyFlow — импорт дедлайнов и оценок")
    parser.add_argument("paths", nargs="*", help="ZIP, папка, messages*.html или Telegram JSON")
    parser.add_argument("--grades", help="Локальная ведомость XLSX")
    parser.add_argument("--schedule", help="Локальное расписание XLSX с листом дедлайны")
    parser.add_argument("--data", default=str(DATA_FILE), help="Путь к файлу данных")
    parser.add_argument("--student", help="Полное ФИО студента")
    parser.add_argument("--no-sync", action="store_true", help="Не синхронизировать при этом запуске")
    parser.add_argument("--no-gui", action="store_true", help="Импорт без графического интерфейса")
    parser.add_argument("--sync", action="store_true", help="Синхронизировать таблицы в консольном режиме")
    parser.add_argument("--export-ics", help="Путь к выходному ICS")
    arguments = parser.parse_args()
    try:
        state = load_data(arguments.data)
        if arguments.student:
            state["settings"]["student_name"] = arguments.student
        if arguments.paths:
            print(import_telegram_data(state, arguments.paths))
        for kind, path in [("grades", arguments.grades), ("deadlines", arguments.schedule)]:
            if path:
                print(import_local_spreadsheet(state, path, kind))
        if arguments.sync:
            print("\n".join(apply_sync_results(state, sync_sources(state["settings"]))))
        statuses_changed = complete_graded_tasks(state)
        if (statuses_changed or arguments.paths or arguments.student or arguments.grades or arguments.schedule or
                arguments.sync or not Path(arguments.data).exists()):
            save_data(state, arguments.data)
        if arguments.export_ics:
            export_ics(state["tasks"], arguments.export_ics)
        if not arguments.no_gui:
            launch_gui(state, arguments.data, skip_sync=arguments.no_sync or arguments.sync)
        return 0
    except Exception as error:
        print("StudyFlow:", error)
        if not arguments.no_gui:
            try:
                import tkinter as tk
                from tkinter import messagebox
                window = tk.Tk()
                window.withdraw()
                messagebox.showerror("StudyFlow", str(error), parent=window)
                window.destroy()
            except Exception:
                pass
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
